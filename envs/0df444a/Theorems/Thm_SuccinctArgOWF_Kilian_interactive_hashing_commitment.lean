-- Prove2me | Theorems.Thm_SuccinctArgOWF_Kilian_interactive_hashing_commitment
-- name    : SuccinctArgOWF.Kilian.interactive_hashing_commitment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:27.044048+00:00
-- url     : https://prove2.me/theorems/398cea5c-752c-4ea4-9ff2-873cca4bc60c
-- title:
--   Theorem 4.1 — constant-round binding commitment compressing by the factor $\gamma=1-\zeta/8$
-- statement:
--   Let $f:\{0,1\}^n\to\{0,1\}^{d(n)}$ be computable in polynomial time and injective, and suppose $f$ is $(2^{\delta n},2^{-\zeta n})$-one-way for all sufficiently large $n$, for constants $\delta,\zeta\in(0,1)$. Let
--
--   $$\ell=10+\max\Bigl\{\Bigl\lceil\frac{40}{\zeta}\Bigr\rceil,\Bigl\lceil\frac{8}{\delta}\Bigr\rceil\Bigr\},\qquad\gamma=1-\frac{\zeta}{8}.$$
--
--   Then there is one sender machine, running in polynomial time, such that for all sufficiently large $n$ the $\ell$-round public-coin commitment for $n$-bit messages with the canonical opening that it defines satisfies:
--
--   1. the committer sends the same number $\tilde d(n)$ of bits in every round and $\ell\,\tilde d(n)\le\gamma n$; in particular it sends at most $\gamma n$ bits;
--   2. every receiver message is a uniformly random string of $O(n)$ bits;
--   3. the commitment is $(2^{\delta n/2},2^{-\zeta n/5})$-binding:
--
--   $$\mathrm{bind}_{\mathrm{Com}}\bigl(2^{\delta n/2}\bigr)\le2^{-\zeta n/5}.$$
--
--   This is the base commitment of the recursive vector commitment: constantly many rounds, compression by a constant factor, binding from exponential hardness.
--
--   **Formalization Note** The canonical verifier recomputes the transcript with the same sender machine, so the receiver is efficient as well. The hypothesis "$d$ polynomially bounded" is implied by polynomial-time computability.
--
--   Differences from the source:
--   - reading: f is (2^{δλ}, 2^{−ζλ})-one-way (no range of λ stated) → f is (2^{δλ}, 2^{−ζλ})-one-way for all sufficiently large λ (Definition 3.2's exponential hardness); reason: the weaker hypothesis, hence the stronger theorem; Definition 3.2 and Theorem 1.1 use this notion
--   - encoding: d = d(n) polynomially bounded → not stated separately; reason: implied by the polynomial-time computability of f (§3.2), so no instance changes
--   - reading: there is an ℓ-round commitment (§3.3: algorithms; canonical opening unless stated otherwise) → a canonical-opening commitment whose sender is a machine running within p(n) steps per round; reason: commitments consist of efficient algorithms; an existence claim about arbitrary functions would not need the one-way function
--   - generalization: for all sufficiently large n there is a commitment → one sender machine, taking n as input, serves all sufficiently large n; reason: a uniform family gives a commitment for each n
--   - generalization: the committer sends at most γn bits; receiver messages of O(n) bits → the committer sends exactly d̃(n) bits in every round with ℓ·d̃(n) ≤ γn; R_j = {0,1}^{m_j(n)} with m_j(n) ≤ C·n; reason: implies the printed bounds; the proof of Corollary 6.3 (p. 20) uses the equal round lengths
--   - reading: non-uniform probabilistic Turing machines with a fixed binary encoding; running time = worst-case steps + description + advice → one machine of the published MetaSearch model with advice per phase of the game, a random tape of length t, cost = total steps + codes and advice of the distinct phase programs, worst case over all coins and all inputs the game can give; reason: the paper fixes no model; a single machine for all phases is the special case
-- source:
--   Jesko Dujmovic, Daniel Wichs, STOC 2027 submission #650 (October 2026), Theorem 4.1, p. 10 (PDF p. 12)

import Mathlib
import Definitions.Def_SuccinctArgOWF_Kilian_OneWay
import Definitions.Def_SuccinctArgOWF_Kilian_Implemented

set_option autoImplicit false

namespace SuccinctArgOWF.Kilian

open MetaSearch.Heyting

/-- Theorem 4.1, Dujmovic–Wichs p.10. Let `f : {0,1}^n → {0,1}^{d(n)}` be computable in polynomial
time, injective and `(2^{δn}, 2^{-ζn})`-one-way for all sufficiently large `n`, with `δ, ζ ∈ (0,1)`.
With `ℓ = 10 + max{⌈40/ζ⌉, ⌈8/δ⌉}` and `γ = 1 − ζ/8`: there is one polynomial-time sender machine
such that, for all sufficiently large `n`, the `ℓ`-round canonical commitment for `n`-bit messages it
defines has a committer sending `d̃(n)` bits in every round with `ℓ·d̃ ≤ γn`, receiver messages of
`O(n)` bits, and is `(2^{δn/2}, 2^{-ζn/5})`-binding. -/
theorem interactive_hashing_commitment (f : Str → Str) (δ ζ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (hζ : 0 < ζ ∧ ζ < 1) (hf : PolyTime f)
    (hlen : ∀ x x' : Str, x.length = x'.length → (f x).length = (f x').length)
    (hinj : ∀ n, InjectiveAt f n) (hexp : ExpHard f δ ζ) :
    let ℓ : ℕ := 10 + max ⌈40 / ζ⌉₊ ⌈8 / δ⌉₊
    let γ : ℝ := 1 - ζ / 8
    ∃ (Snd : Machine) (p : Polynomial ℕ) (C : ℕ) (m : ℕ → Fin ℓ → ℕ) (dt : ℕ → ℕ) (n₀ : ℕ),
      ∀ n ≥ n₀,
        (∀ x : Str, x.length = n → ∀ ρ : (canonFamily Snd n ℓ (m n)).Coins, ∀ j : Fin ℓ,
          HaltsAt Snd (sndIns n j.1 (senderState (canonFamily Snd n ℓ (m n)).init
            (canonFamily Snd n ℓ (m n)).S x ((canonFamily Snd n ℓ (m n)).cs ρ) j.1) (ρ j).1)
            (p.eval n)) ∧
        ((ℓ : ℝ) * (dt n : ℝ) ≤ γ * (n : ℝ) ∧ (canonFamily Snd n ℓ (m n)).MsgLen (dt n)) ∧
        (∀ j, m n j ≤ C * n) ∧
        (canonFamily Snd n ℓ (m n)).bind ⌊(2 : ℝ) ^ (δ * n / 2)⌋₊ ≤ (2 : ℝ) ^ (-(ζ * n / 5)) := by sorry

end SuccinctArgOWF.Kilian
