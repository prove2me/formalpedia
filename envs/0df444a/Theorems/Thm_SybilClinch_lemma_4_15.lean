-- Prove2me | Theorems.Thm_SybilClinch_lemma_4_15
-- name    : SybilClinch.lemma_4_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:45:22.656731+00:00
-- url     : https://prove2.me/theorems/54c65161-2ff9-47c4-aaf0-b7df04171cfe
-- title:
--   Lemma 4.15 — mark-to-market identity $\Gamma_I(p)=\int_{p_\star}^p X_I$
-- statement:
--   In a completed run of an admissible abstract target-based mechanism, let $I$ be any set of identities, with cumulative allocation $X_I$ and payment $Y_I$ (constant after the run ends), and $\Gamma_I(p)=pX_I(p)-Y_I(p)$. Under current-price charging,
--   $$\Gamma_I(p)=\int_{p_\star}^{p}X_I(s)\,ds\qquad(p\ge p_\star).$$
--   In particular $\Gamma_I$ is continuous across fixed-price purchases and locally absolutely continuous on $[p_\star,\infty)$, with derivative $X_I$ almost everywhere. If every identity in $I$ reports a value at most $V$, then its aggregate true utility $V X_I(p_f)-Y_I(p_f)$ equals $\Gamma_I(V)$.
--
--   Differences from the source:
--   - reading: continuous evolution by the primitive conditions (16)–(18) on event-free open intervals, on which the clock and state paths are absolutely continuous → IsRun: the event procedure is applied at every clock price; off Clinch the continuous part of dx_i has no mass; a clincher stays at the water level on a right neighbourhood of every price while active; no absolute-continuity requirement on the paths; reason: event prices may accumulate (lumps of an admissible target can be dense) and, for an admissible AMM whose right marginal ask is flat on a fat Cantor set, the sole-survivor path X = Z(p) is continuous but not absolutely continuous, so a literal AC requirement would admit no run; on event-free intervals with AC paths the two formulations coincide
--   - encoding: Γ_I continuous and locally absolutely continuous, with derivative X_I a.e. → ContinuousOn on [p⋆, ∞), AbsolutelyContinuousOnInterval on every [a, b] ⊆ [p⋆, ∞), HasDerivAt with value X_I(p) for a.e. p > p⋆; reason: the run starts at p⋆; same content
--   - generalization: reported values (v_i, q_i) ∈ ℝ²≥0 (the one-sided analysis of §4 allows only finite values, p.28) → values in WithTop ℝ, +∞ allowed (no hypothesis v_i ≠ ⊤); reason: values enter the mechanism only through exits, and the paper itself applies these structural lemmas to runs with infinite reports (proof of Lemma 6.2, p.28); on finite-value profiles the statement is the source's
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §4.6, Lemma 4.15, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_SybilClinch_IsRun
import Definitions.Def_SybilClinch_TargetMech_Admissible
import Definitions.Def_SybilClinch_OneSidedProfile_Valid
import Definitions.Def_SybilClinch_Run_gain

set_option autoImplicit false

open Filter Topology Set MeasureTheory

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §4.6, Lemma 4.15 (Mark-to-market identity), printed p.22 (PDF p.24).

Under current-price charging, for every set `I` of identities and every `p ≥ p⋆`,
`Γ_I(p) = ∫_{p⋆}^{p} X_I(s) ds`. In particular `Γ_I` is continuous across fixed-price
purchases and locally absolutely continuous, with derivative `X_I` almost everywhere. If every
identity in `I` reports at most `V`, its aggregate true utility `V·X_I − Y_I` (terminal allocation
and payment) equals `Γ_I(V)`.

**Formalization Note.** `X_I`, `Y_I` are extended constantly after the run ends (`IsRun.const_after`). -/
theorem lemma_4_15 (M : TargetMech) (hM : M.Admissible) (P : OneSidedProfile) (hP : P.Valid)
    (R : Run) (hR : IsRun M P R) (I : Finset ℕ) (hI : I ⊆ P.ids) :
    (∀ p, M.pstar ≤ p → R.gain M I p = ∫ s in M.pstar..p, R.alloc I s) ∧
    ContinuousOn (R.gain M I) (Ici M.pstar) ∧
    (∀ a b, M.pstar ≤ a → a ≤ b → AbsolutelyContinuousOnInterval (R.gain M I) a b) ∧
    (∀ᵐ p, M.pstar < p → HasDerivAt (R.gain M I) (R.alloc I p) p) ∧
    ∀ V : ℝ, (∀ i ∈ I, P.v i ≤ (V : WithTop ℝ)) →
      V * R.alloc I R.pf - R.payOf M I R.pf = R.gain M I V := by sorry

end SybilClinch
