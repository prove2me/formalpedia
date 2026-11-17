-- Prove2me | Theorems.Thm_ProofCryptoSynergy_Supplement_theorem_64
-- name    : ProofCryptoSynergy.Supplement.theorem_64
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:55:08.301952+00:00
-- url     : https://prove2.me/theorems/d3583ce8-c624-42bb-97a0-7f541d5ee2a0
-- title:
--   Theorem 64 — non-NP-hardness of Total-Learn under Levin reductions
-- statement:
--   Assume that subexponentially secure iO and subexponentially secure one-way functions exist. Then there is a polynomial $g$ such that for every polynomial $s$ and every $\varepsilon\le1/2$, $\mathrm{Total\text{-}Learn}_{g,\varepsilon}[s]$ is not NP-hard under nonuniform or randomized subexponential-time Levin reductions: SAT has
--
--   1. no nonuniform Levin reduction of subexponential circuit size, and
--   2. no randomized Levin reduction of subexponential running time (error $1/100$)
--
--   to $\mathrm{Total\text{-}Learn}_{g,\varepsilon}[s]$.
--
--   Together with Theorem 46 it separates half-Levin from Levin NP-hardness of learning.
--
--   Differences from the source:
--   - encoding: polynomial p(n) = n^c, c ≥ 1, with parameters s, g, ε⁻¹ : ℕ → ℕ → IsPolyFn: n ↦ ⌊n^c⌋, real c ≥ 1; reason: Definitions 21–27 take the parameters ℕ-valued; circuit sizes are naturals, so the floor changes no bound
--   - encoding: Pr < 1/2 + ε(n) → (Pr − 1/2)·ε⁻¹(n) < 1, the parameter being ε⁻¹ : ℕ → ℕ; reason: Definition 21 takes ε⁻¹ as the parameter; no division, and ε⁻¹(n) = 0 (ε undefined) is not the hardest case
--   - encoding: promise problems over strings (Definition 3); SAT with witness relation φ(w) = 1 → witness relations on sampling circuits and circuits, R_N containing the invalid instances; SAT witnesses with |w| ≤ |φ|; reason: N is exactly the set of no-instances; every variable index of φ is below |φ|, so SAT’s Y and N are unchanged
--   - encoding: randomized reduction (ε unspecified) → error 1/100; reason: p.17: if ε is not specified, ε = 1/100
--   - reading: Definition 5, condition 1, for every x ∈ Y₁ (w free) → for every (x, w) ∈ R_Y; reason: w is bound by R_Y as in Definition 4’s witness mapping
--   - encoding: a poly(n)-size circuit E sampling (x, b) → every output of the reduction has description length at most (n+2)^c, n its input length, for one constant c (PolySizeOut / RandPolySizeOut); reason: “poly(n)-size” names no polynomial, so one polynomial per reduction; n + 2 avoids the zero bound at n = 0
--   - encoding: ε ≤ 1/2 → ε⁻¹(n) ≥ 2 for all n; reason: the same condition on the parameter ε⁻¹
--   - encoding: nonuniform or randomized subexponential-time Levin reductions → nonuniform: circuits of size t(|x|); randomized: machines of t(|x|) steps; t with the published IsSubexp; reason: Definitions 4 and 5 with a subexponential bound
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Theorem 64, p.50 (PDF 52)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_IsSubexp
import Definitions.Def_ProofCryptoSynergy_SubexpIOExists
import Definitions.Def_ProofCryptoSynergy_SubexpOWFExists
import Definitions.Def_ProofCryptoSynergy_Supplement_IsPolyFn
import Definitions.Def_ProofCryptoSynergy_Supplement_CGL
import Definitions.Def_ProofCryptoSynergy_Supplement_DetHalfLevin

open KarpLiptonOM LaconicBarrier ProofCryptoSynergy

namespace ProofCryptoSynergy.Supplement

/-- **Theorem 64 (Non-NP-hardness of Total-Learn under Levin reductions)** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.50 (PDF 52)).
Assume that subexponentially secure iO and subexponentially secure one-way functions exist. Then there exists
a polynomial `g` such that for every polynomial `s` and `ε ≤ 1/2`, `Total-Learn_{g,ε}[s]` is not NP-hard under
nonuniform or randomized subexponential-time Levin reductions.

**Formalization Note** Both negations are stated: SAT has no nonuniform Levin reduction of subexponential
circuit size and no randomized Levin reduction of subexponential running time with error `1/100` (the default
of p.17). `ε ≤ 1/2` is `ε⁻¹(n) ≥ 2` for all `n`. Honesty is not assumed (the theorem covers all reductions). A reduction to Total-Learn outputs its
instances, samplers of polynomial size in their input length (`PolySizeOut`, `RandPolySizeOut`;
Definition 23: "a poly(n)-size circuit `E`"). -/
theorem theorem_64 :
    SubexpIOExists → SubexpOWFExists →
      ∃ g : ℕ → ℕ, IsPolyFn g ∧ ∀ s εinv : ℕ → ℕ, IsPolyFn s → (∀ n, 2 ≤ εinv n) →
        (¬ ∃ (t : ℕ → ℕ) (f : List Bool → Samp) (gw : List Bool → List Bool → Wit)
            (h : List Bool → Wit → List Bool),
            IsSubexp (fun n => (t n : ℝ)) ∧ NonuLevin (TotalLearn s g εinv) t f gw h ∧ PolySizeOut f) ∧
        (¬ ∃ (t ρ ρ₂ : ℕ → ℕ) (f : List Bool → List Bool → Samp)
            (gw : List Bool → List Bool → List Bool → Wit)
            (h : List Bool → Wit → List Bool → List Bool → List Bool),
            IsSubexp (fun n => (t n : ℝ)) ∧
              RandLevin (TotalLearn s g εinv) t (1 / 100) ρ ρ₂ f gw h ∧ RandPolySizeOut ρ f) := by sorry

end ProofCryptoSynergy.Supplement
