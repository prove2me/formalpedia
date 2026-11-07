-- Prove2me | Theorems.Thm_SamplingAC0_hard_distribution_facts
-- name    : SamplingAC0.hard_distribution_facts
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:47:46.589127+00:00
-- url     : https://prove2.me/theorems/b373e9d4-2290-41b6-baa0-e1076313ed9a
-- title:
--   §3, p.8 — incidences, the DNF sampler of $R$, and $\mathbb P[C_\ell=0]=(1-1/q)^q\ge1/4$
-- statement:
--   Let $q=2^k$ with $k\ge1$ and fix any encoding of $\mathbb F_q$ by $k$-bit strings. Then:
--
--   1. each nonvertical line of $\mathbb F_q^2$ contains $q$ points;
--   2. each point of $\mathbb F_q^2$ lies on $q$ nonvertical lines;
--   3. two distinct lines share at most one point;
--   4. the line DNF $C_\ell$ is true on an input exactly when some listed point lies on $\ell$;
--   5. $C_\ell$ has $q^2$ terms, each with $2k$ literals;
--   6. every output of the block sampler is a DNF of size at most $q^c$, for an absolute constant $c>0$;
--   7. the block sampler applied to uniform input bits samples exactly $R$;
--   8. for every line $\ell$,
--   $$\mathbb P_R[C_\ell=0]=(1-1/q)^q\ \ge\ 1/4 .$$
--
--   These are the facts about the hard distribution that the rest of the proof uses: the incidence structure of points and lines, that $R$ is sampled by explicit DNFs, and that each line bit is $0$ with constant probability.
--
--   **Formalization Note** DNF size counts terms and literal occurrences; the constant $c$ is chosen before $k$ and the encoding.
--
--   Differences from the source:
--   - generalization: points recorded with 2k bits by one unnamed encoding → every bijection enc : F_q ≃ {0,1}^k; reason: the facts hold for each encoding, in particular the paper's
--   - encoding: q a power of two; "explicit DNF with q² terms"; "size q^c" → q = 2^k with k ≥ 1; length q² with 2k literals per term; size (terms + literal occurrences) ≤ (2^k)^c with c before k; reason: F_1 does not exist; the size measure is at least the term count
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), §3, p.8 (the hard distribution)

import Mathlib
import Definitions.Def_SamplingAC0_law
import Definitions.Def_SamplingAC0_DNF
import Definitions.Def_SamplingAC0_lineDNF
import Definitions.Def_SamplingAC0_R
set_option autoImplicit false

namespace SamplingAC0

/-- **The hard distribution: incidences, its DNF sampler, and `P[C_ℓ = 0]`.** Riazanov–Viola,
*Sampling Tools and the Power of AC0*, STOC 2027 submission (manuscript sha256 99c33d30…), §3, p.8:
"Each line contains q points, each point lies on q lines, and two distinct lines intersect in at
most one point. […] To compute C_ℓ, take an OR over the q list positions and the q locations on ℓ,
testing equality of their 2k bits. This is an explicit DNF with q² terms. The point-coordinate
outputs are input bits. Every output is therefore sampled by an explicit DNF of size q^c. For every
line ℓ, P[C_ℓ = 0] = (1 − 1/q)^q ≥ 1/4."

For `q = 2^k`, `k ≥ 1`, and every encoding of field elements by `k` bits.

**Formalization Note.** DNF size counts terms and literal occurrences; the constant `c` comes
before `k` and the encoding. The seventh clause says the DNF sampler `blockSampler` samples
exactly `R`. -/
theorem hard_distribution_facts : ∃ c : ℝ, 0 < c ∧ ∀ (enc : Encoding) (k : ℕ), 1 ≤ k →
    (∀ ℓ : Line k, Fintype.card {v : F k × F k // onLine ℓ v} = 2 ^ k) ∧
    (∀ v : F k × F k, Fintype.card {ℓ : Line k // onLine ℓ v} = 2 ^ k) ∧
    (∀ ℓ ℓ' : Line k, ℓ ≠ ℓ' → Fintype.card {v : F k × F k // onLine ℓ v ∧ onLine ℓ' v} ≤ 1) ∧
    (∀ (ℓ : Line k) (x : RIn k → Bool),
      (lineDNF enc ℓ).eval x = decide (∃ i, onLine ℓ (decodePt enc x i))) ∧
    (∀ ℓ : Line k, (lineDNF enc ℓ).length = (2 ^ k) ^ 2 ∧ ∀ t ∈ lineDNF enc ℓ, t.length = 2 * k) ∧
    (∀ o : ROut k, ((blockSampler enc k o).size : ℝ) ≤ ((2 : ℝ) ^ k) ^ c) ∧
    law (fun x : RIn k → Bool => fun o => (blockSampler enc k o).eval x) = R enc k ∧
    (∀ ℓ : Line k, pr (R enc k) {y | y (Sum.inl ℓ) = false} = (1 - 1 / (2 : ℝ) ^ k) ^ (2 ^ k)) ∧
    (1 - 1 / (2 : ℝ) ^ k) ^ (2 ^ k) ≥ 1 / 4 := by sorry

end SamplingAC0
