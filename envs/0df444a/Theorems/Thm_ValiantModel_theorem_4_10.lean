-- Prove2me | Theorems.Thm_ValiantModel_theorem_4_10
-- name    : ValiantModel.theorem_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:38:50.293085+00:00
-- url     : https://prove2.me/theorems/219108d3-4252-4fc0-89bf-71d4cf9ec053
-- title:
--   Theorem 4.10, p.28 — VC lower bound for Valiant's model
-- statement:
--   If $H$ has a learner with sample/query complexity $m$, then for every $d\ge 1$ and every $\varepsilon,\delta\in(0,1/2)$,
--
--   $$
--   m(d,\varepsilon,\delta)\ge\frac{\mathrm{VC}(H_d)-1}{9}.
--   $$
--
--   In particular, if $H$ is learnable in Valiant's model, then $\mathrm{VC}(H_d)=\mathrm{poly}(d)$.
--
--   Finite VC dimension is therefore necessary, with a polynomial bound, and this supplies the factor $\mathrm{VC}(H_d)$ needed to turn Theorem 4.6 into a polynomial bound.
--
--   **Formalization Note** The subtraction is in the reals, so the value $\mathrm{VC}(H_d)=0$ gives the true bound $-1/9$, and $m=0$ is included.
--
--   Differences from the source:
--   - generalization: H learnable in Valiant's model with complexity m, polynomial → in the first clause, any learner with any complexity function (`HasComplexity`); reason: the argument does not use the polynomial bound; the second clause keeps `Learnable`
--   - encoding: VC(Hd) = poly(d) → `∃ C k : ℕ, ∀ d ≥ 1, VC ≤ C * d ^ k`; reason: for d ≥ 1 a monomial bound is equivalent to a polynomial bound
--   - encoding: VC(Hd) → `(vcDim (H d)).toNat`; reason: vcDim is finite on the finite domain (checked in the sanity file), so `toNat` loses nothing
--   - encoding: a randomized learner with internal randomness → a `PMF` over deterministic protocols on each input (`Learner`); reason: fixing the internal randomness gives a deterministic protocol (p.15), and with a bounded budget on a finite domain only finitely many protocols are distinct; no learner is lost
--   - encoding: at most m(d, ε, δ) positive examples and membership queries → at most m(d, ε, δ) calls on each oracle, on every path of every protocol in the support (`WithinBudget`); reason: this is the paper's own count (Remark 3.1, p.15; proof of Theorem 4.10, p.28)
--   - encoding: d ∈ N, with the sequence starting at H₁ → `1 ≤ d`; reason: the sequence is indexed from 1; `H 0` is not part of the source
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), p.28 (PDF p.30), Theorem 4.10

import Mathlib
import Definitions.Def_HighDimProb_Chaining_VcDim
import Definitions.Def_ValiantModel_Learnable

open HighDimProb.Chaining

namespace ValiantModel

/-- **Theorem 4.10 (VC Lower Bound for Valiant's Model)**, arXiv:2605.13840 (version held), p.28
(PDF p.30). For every `d` and `ε, δ ∈ (0, 1/2)`, `m(d, ε, δ) ≥ (VC(Hd) - 1) / 9`; and if `H` is
learnable then `VC(Hd) = poly(d)`.

**Formalization Note.** `m` counts each oracle separately, as the proof does (p.28). `m = 0` is
included. `VC(Hd)` is the `toNat` of `vcDim`, finite on the finite domain, and the subtraction is in
`ℝ`. The first clause holds for any complexity function. `poly(d)` is `C * d ^ k`, equivalent since
`d ≥ 1`. -/
theorem theorem_4_10 (H : ConceptSequence) :
    (∀ (L : Learner) (m : ℕ → ℝ → ℝ → ℕ), HasComplexity H L m →
      ∀ d : ℕ, 1 ≤ d → ∀ ε δ : ℝ, 0 < ε → ε < 1 / 2 → 0 < δ → δ < 1 / 2 →
        (((vcDim (H d)).toNat : ℝ) - 1) / 9 ≤ (m d ε δ : ℝ)) ∧
    (Learnable H → ∃ C k : ℕ, ∀ d : ℕ, 1 ≤ d → (vcDim (H d)).toNat ≤ C * d ^ k) := by sorry

end ValiantModel
