-- Prove2me | Theorems.Thm_SuccinctArgOWF_Kilian_vector_commitment
-- name    : SuccinctArgOWF.Kilian.vector_commitment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:42.848964+00:00
-- url     : https://prove2.me/theorems/b6dd0800-b79f-4563-a606-68ef6230be9d
-- title:
--   Corollary 6.3 — interactive vector commitment from exponentially hard injective one-way functions
-- statement:
--   Let $f:\{0,1\}^\lambda\to\{0,1\}^{d(\lambda)}$ be computable in polynomial time and injective, and $(2^{\delta\lambda},2^{-\zeta\lambda})$-one-way for all sufficiently large $\lambda$, for constants $\delta,\zeta\in(0,1)$. Let
--
--   $$\ell=10+\max\Bigl\{\Bigl\lceil\frac{40}{\zeta}\Bigr\rceil,\Bigl\lceil\frac{8}{\delta}\Bigr\rceil\Bigr\},\qquad\gamma=1-\frac{\zeta}{8},\qquad\theta=\frac{\log\ell}{\log(\ell/\gamma)} .$$
--
--   Then $\theta<1$, and there are one sender machine and one receiver machine, both taking $N$ as input, defining a public-coin commitment $\mathrm{Com}$ with interval opening for messages in $\{0,1\}^N$ such that, for all sufficiently large $N$:
--
--   1. $\mathrm{Com}$ is complete and has $O(N^\theta/(\log N)^{3\theta})$ rounds;
--   2. the total communication (both directions) for the commitment and an opening of one position is $O\bigl(N^\theta(\log N)^{3(1-\theta)}\bigr)=\tilde O(N^\theta)$;
--   3. the honest sender runs in time polynomial in $N$, and the receiver's total running time for the commitment and the verification of one position opening is $\tilde O(N^\theta)$;
--
--   and for every polynomial $t$, for all sufficiently large $N$:
--
--   4. the selective interval binding error, and hence the selective position binding error, satisfies
--
--   $$\mathrm{bind}^{\mathrm{int}}_{\mathrm{Com}}(t(N))\le2^{-(\log N)^2}=\mathrm{negl}(N);$$
--
--   5. every adversary of running time $t(N)$ wins the adaptive interval binding game, and the adaptive position binding game, with probability at most $N^2\cdot2^{-(\log N)^2}$.
--
--   This is the formal version of Theorem 1.2: a succinct interactive vector commitment with adaptive position binding from exponentially hard injective one-way functions.
--
--   **Formalization Note** Logarithms are base $2$. The receiver's messages are uniformly random strings whose lengths its machine announces from $N$; its time bound is a worst case over all sender messages and proofs.
--
--   Differences from the source:
--   - reading: f is (2^{δλ}, 2^{−ζλ})-one-way (no range of λ stated) → f is (2^{δλ}, 2^{−ζλ})-one-way for all sufficiently large λ (Definition 3.2's exponential hardness); reason: the weaker hypothesis, hence the stronger theorem; Definition 3.2 and Theorem 1.1 use this notion
--   - generalization: for all sufficiently large N there is a commitment Com with poly(N) sender and Õ(N^θ) receiver → one sender machine and one receiver machine, taking N as input, define Com for every N; reason: a uniform family gives a commitment for each N; Corollary 6.5 runs it
--   - generalization: public-coin commitment (finite sets R_j) → R_j = {0,1}^{m_j}, with the number of rounds and the lengths m_j computed by the receiver machine from N; reason: a special case of finite sets, so the Lean conclusion implies the printed one
--   - encoding: O(·) and Õ(N^θ) bounds → C·N^θ/(log N)^{3θ}, C·N^θ(log N)^{3(1−θ)}, C·N^θ(log N)^c for N ≥ N₀, with constants C, c; reason: explicit constants for the asymptotic bounds
--   - encoding: total communication for the commitment and an opening of one position → Σ|r_j| + Σ|y_j| + 1 + |π| for the honest opening π of position i; reason: receiver messages, sender messages, the opened bit and its proof
--   - reading: the honest sender runs in time polynomial in N → every round and every interval opening halts within p(N) steps, and their total is at most p(N); reason: polynomial total time of the honest sender
--   - reading: the receiver's total running time for the commitment and verification of one position opening is Õ(N^θ) → schedule queries plus the verification run, for all coins, all sender messages, values and proofs; reason: worst case over the sender's behaviour
--   - encoding: θ = log ℓ / log(ℓ/γ) < 1 → the clause θ < 1 stated as part of the conclusion; reason: the printed statement asserts it
--   - reading: non-uniform probabilistic Turing machines with a fixed binary encoding; running time = worst-case steps + description + advice → one machine of the published MetaSearch model with advice per phase of the game, a random tape of length t, cost = total steps + codes and advice of the distinct phase programs, worst case over all coins and all inputs the game can give; reason: the paper fixes no model; a single machine for all phases is the special case
-- source:
--   Jesko Dujmovic, Daniel Wichs, STOC 2027 submission #650 (October 2026), Corollary 6.3, p. 20 (PDF p. 22)

import Mathlib
import Definitions.Def_SuccinctArgOWF_Kilian_OneWay
import Definitions.Def_SuccinctArgOWF_Kilian_Implemented

set_option autoImplicit false

namespace SuccinctArgOWF.Kilian

open MetaSearch.Heyting

/-- Corollary 6.3 (vector commitment), Dujmovic–Wichs p.20. Let `f` be polynomial-time computable,
injective and `(2^{δλ}, 2^{-ζλ})`-one-way for all sufficiently large `λ`, with `δ, ζ ∈ (0,1)`, and
`ℓ = 10 + max{⌈40/ζ⌉, ⌈8/δ⌉}`, `γ = 1 − ζ/8`, `θ = log ℓ / log(ℓ/γ)`. Then `θ < 1`, and one uniform
sender machine and one uniform receiver machine define, for every `N`, a public-coin commitment with
interval opening for `{0,1}^N` such that for all sufficiently large `N`: it is complete, has
`O(N^θ/(log N)^{3θ})` rounds, total communication `O(N^θ (log N)^{3(1−θ)})` for the commitment and
the opening of one position, a sender running in time polynomial in `N` and a receiver whose total
time for the commitment and the verification of one position opening is `O(N^θ (log N)^c)`; and for
every polynomial `t`, for all sufficiently large `N`, `bind^int_Com(t(N)) ≤ 2^{-(log N)²}`, the
selective position binding error is at most `2^{-(log N)²}`, and every adversary of running time
`t(N)` wins the adaptive interval and the adaptive position binding game with probability at most
`N² · 2^{-(log N)²}`. -/
theorem vector_commitment (f : Str → Str) (δ ζ : ℝ) (hδ : 0 < δ ∧ δ < 1) (hζ : 0 < ζ ∧ ζ < 1)
    (hf : PolyTime f) (hlen : ∀ x x' : Str, x.length = x'.length → (f x).length = (f x').length)
    (hinj : ∀ n, InjectiveAt f n) (hexp : ExpHard f δ ζ) :
    let ℓ : ℕ := 10 + max ⌈40 / ζ⌉₊ ⌈8 / δ⌉₊
    let γ : ℝ := 1 - ζ / 8
    let θ : ℝ := Real.logb 2 ℓ / Real.logb 2 (ℓ / γ)
    θ < 1 ∧
    ∃ (Snd Rcv : Machine) (C c : ℝ) (p : Polynomial ℕ) (N₀ : ℕ),
      (∀ N ≥ N₀,
        SchedOK Rcv [natBits N] ∧
        (machineVC Snd Rcv N).Complete ∧
        ((machineVC Snd Rcv N).ℓ : ℝ) ≤ C * (N : ℝ) ^ θ / (Real.logb 2 N) ^ (3 * θ) ∧
        (∀ (m : Str), m.length = N → ∀ ρ : (machineVC Snd Rcv N).Coins,
          (∀ j : Fin (machineVC Snd Rcv N).ℓ,
            HaltsAt Snd (sndIns N j.1 (senderState (machineVC Snd Rcv N).init
              (machineVC Snd Rcv N).S m ((machineVC Snd Rcv N).cs ρ) j.1) (ρ j).1) (p.eval N)) ∧
          (∀ a b, IsInterval N a b →
            HaltsAt Snd (openIns N ((machineVC Snd Rcv N).final m ((machineVC Snd Rcv N).cs ρ)) a b)
                (p.eval N) ∧
              (List.ofFn fun j : Fin (machineVC Snd Rcv N).ℓ => time Snd (sndIns N j.1
                (senderState (machineVC Snd Rcv N).init (machineVC Snd Rcv N).S m
                  ((machineVC Snd Rcv N).cs ρ) j.1) (ρ j).1)).sum +
                time Snd (openIns N ((machineVC Snd Rcv N).final m ((machineVC Snd Rcv N).cs ρ))
                  a b) ≤ p.eval N) ∧
          ∀ i, 1 ≤ i → i ≤ N →
            ((List.ofFn fun j : Fin (machineVC Snd Rcv N).ℓ => (ρ j).1.length).sum +
              (List.ofFn fun j => ((machineVC Snd Rcv N).tr m ((machineVC Snd Rcv N).cs ρ) j).length).sum +
              1 + ((machineVC Snd Rcv N).Open
                ((machineVC Snd Rcv N).final m ((machineVC Snd Rcv N).cs ρ)) i i).length : ℝ) ≤
              C * (N : ℝ) ^ θ * (Real.logb 2 N) ^ (3 * (1 - θ))) ∧
        ∀ (ρ : (machineVC Snd Rcv N).Coins) (τ : Fin (machineVC Snd Rcv N).ℓ → Str) (i : ℕ)
          (v π : Str), 1 ≤ i → i ≤ N →
          Halts Rcv (rcvIns N (List.ofFn ((machineVC Snd Rcv N).cs ρ)) (List.ofFn τ) i i v π) ∧
            ((schedTime Rcv [natBits N] +
              time Rcv (rcvIns N (List.ofFn ((machineVC Snd Rcv N).cs ρ)) (List.ofFn τ) i i v π) :
                ℕ) : ℝ) ≤ C * (N : ℝ) ^ θ * (Real.logb 2 N) ^ c) ∧
      (∀ t : Polynomial ℕ, ∀ᶠ N in Filter.atTop,
        (machineVC Snd Rcv N).bindInt (t.eval N) ≤ (2 : ℝ) ^ (-(Real.logb 2 N) ^ 2)) ∧
      (∀ t : Polynomial ℕ, ∀ᶠ N in Filter.atTop, ∀ A : Adv,
        A.RunsWithin (t.eval N) [] (Set.range (machineVC Snd Rcv N).selSched) →
          (machineVC Snd Rcv N).selProb true A (t.eval N) ≤ (2 : ℝ) ^ (-(Real.logb 2 N) ^ 2)) ∧
      (∀ t : Polynomial ℕ, ∀ᶠ N in Filter.atTop, ∀ A : Adv,
        A.RunsWithin (t.eval N) [] (Set.range (machineVC Snd Rcv N).adaSched) →
          (machineVC Snd Rcv N).adaProb false A (t.eval N) ≤
              (N : ℝ) ^ 2 * (2 : ℝ) ^ (-(Real.logb 2 N) ^ 2) ∧
            (machineVC Snd Rcv N).adaProb true A (t.eval N) ≤
              (N : ℝ) ^ 2 * (2 : ℝ) ^ (-(Real.logb 2 N) ^ 2)) := by sorry

end SuccinctArgOWF.Kilian
