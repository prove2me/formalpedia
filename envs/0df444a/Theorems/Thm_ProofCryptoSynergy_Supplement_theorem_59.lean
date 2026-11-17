-- Prove2me | Theorems.Thm_ProofCryptoSynergy_Supplement_theorem_59
-- name    : ProofCryptoSynergy.Supplement.theorem_59
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:54:19.655502+00:00
-- url     : https://prove2.me/theorems/6876c260-e454-44d0-81f2-12e00ee815e5
-- title:
--   Theorem 59 — NP-hardness of Gap-ImpMCSP from iO, NIWI and no i.o. optimal proof system
-- statement:
--   Assume that subexponentially secure iO and a subexponentially secure NIWI exist, and that there is no infinitely-often subexponentially optimal proof system. Then there is a polynomial $s'$ such that for all subexponential functions $g'$ and $(\varepsilon')^{-1}$,
--   $$\mathrm{Gap}_{g',\varepsilon'}\text{-ImpMCSP}[s']\ \text{is NP-hard under deterministic polynomial-time half-Levin reductions.}$$
--
--   Here the sampled distributions define total boolean functions, which upgrades Theorem 46 from learning to implicit MCSP.
--
--   Differences from the source:
--   - encoding: polynomial p(n) = n^c, c ≥ 1, with parameters s, g, ε⁻¹ : ℕ → ℕ → IsPolyFn: n ↦ ⌊n^c⌋, real c ≥ 1; reason: Definitions 21–27 take the parameters ℕ-valued; circuit sizes are naturals, so the floor changes no bound
--   - encoding: Pr < 1/2 + ε(n) → (Pr − 1/2)·ε⁻¹(n) < 1, the parameter being ε⁻¹ : ℕ → ℕ; reason: Definition 21 takes ε⁻¹ as the parameter; no division, and ε⁻¹(n) = 0 (ε undefined) is not the hardest case
--   - encoding: promise problems over strings (Definition 3); SAT with witness relation φ(w) = 1 → witness relations on sampling circuits and circuits, R_N containing the invalid instances; SAT witnesses with |w| ≤ |φ|; reason: N is exactly the set of no-instances; every variable index of φ is below |φ|, so SAT’s Y and N are unchanged
--   - encoding: polynomial-time (runtime at most n^c) → step bound (n+2)^c in |φ|, c ∈ ℕ, on the published OracleTM; reason: the same class of bounds; avoids the zero bound at n = 0
--   - encoding: subexponential g′, (ε′)⁻¹ → g′, ε′⁻¹ : ℕ → ℕ with the published IsSubexp (eventual bound 2^{n^{1/c}} for each c); reason: the base mission’s reading of §2.1; no positivity is added, the problems are monotone
--   - encoding: a poly(n)-size circuit E sampling (x, b) → every output of the reduction has description length at most (n+2)^c, n its input length, for one constant c (PolySizeOut / RandPolySizeOut); reason: “poly(n)-size” names no polynomial, so one polynomial per reduction; n + 2 avoids the zero bound at n = 0
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Theorem 59, p.47 (PDF 49)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_IsSubexp
import Definitions.Def_ProofCryptoSynergy_SubexpIOExists
import Definitions.Def_ProofCryptoSynergy_NIWIScheme
import Definitions.Def_ProofCryptoSynergy_NoIoSubexpOptimalPPS
import Definitions.Def_ProofCryptoSynergy_Supplement_IsPolyFn
import Definitions.Def_ProofCryptoSynergy_Supplement_CGL
import Definitions.Def_ProofCryptoSynergy_Supplement_DetHalfLevin

open KarpLiptonOM LaconicBarrier ProofCryptoSynergy

namespace ProofCryptoSynergy.Supplement

/-- **Theorem 59 (NP-hardness of Gap-ImpMCSP)** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.47 (PDF 49)). Assume subexponentially secure iO and a subexponentially secure NIWI exist and
there is no infinitely-often subexponentially optimal proof system. Then there exists a polynomial `s'` such
that `Gap_{g',ε'}-ImpMCSP[s']` is NP-hard under deterministic polynomial-time half-Levin reductions, for
arbitrary subexponential `g'`, `(ε')⁻¹`.

**Formalization Note** `s'` is chosen before `g'` and `(ε')⁻¹`; the reduction may depend on them.
"Subexponential" is the published `IsSubexp` (no positivity is required: the problems are monotone).
"Polynomial-time" is a step bound `(n+2)^c` in `|φ|`.
The output samplers are instances of polynomial size in their input length (`PolySizeOut`; the
definitions of the learning problems: "a poly(n)-size circuit `E`"). -/
theorem theorem_59 :
    SubexpIOExists → SubexpNIWIExists → NoIoSubexpOptimalPPS →
      ∃ s : ℕ → ℕ, IsPolyFn s ∧ ∀ g εinv : ℕ → ℕ,
        IsSubexp (fun n => (g n : ℝ)) → IsSubexp (fun n => (εinv n : ℝ)) →
        ∃ (c : ℕ) (f : List Bool → Samp) (gw : List Bool → List Bool → Wit),
          DetHalfLevin (GapImpMCSP s g εinv) (fun n => (n + 2) ^ c) f gw ∧ PolySizeOut f := by sorry

end ProofCryptoSynergy.Supplement
