-- Prove2me | Theorems.Thm_SybilClinch_lemma_4_8
-- name    : SybilClinch.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:44:54.769359+00:00
-- url     : https://prove2.me/theorems/324cdbb6-1743-442e-b5e5-3e612eb4d45c
-- title:
--   Lemma 4.8 — allocation structure and clincher persistence in a continuing run
-- statement:
--   Consider a completed run of an admissible abstract target-based mechanism and a clock price $p\in[p_\star,p_f)$ at which the run continues. Then:
--
--   1. the supply invariant $S\le D_{-i}$ ($i\in\mathrm{Active}$), with $D_{-i}=\sum_{j\ne i,\,b_j>0}b_j/p$, is equivalent to $b_i\le h$ ($i\in\mathrm{Active}$), and $\{i\in\mathrm{Active}:S=D_{-i}\}=\{i\in\mathrm{Active}:b_i=h\}$ (39);
--   2. an identity that has never clinched through $p$ has received no allocation and made no payment;
--   3. once an identity clinches, it remains a clincher until the run ends;
--   4. no positive effective budget is exhausted: every identity with $v_i>p$ and $q_i>0$ is active, and
--   $$b_i=\min\{q_i,h\}\qquad(i\in\mathrm{Active}).\qquad(40)$$
--
--   Differences from the source:
--   - reading: continuous evolution by the primitive conditions (16)–(18) on event-free open intervals, on which the clock and state paths are absolutely continuous → IsRun: the event procedure is applied at every clock price; off Clinch the continuous part of dx_i has no mass; a clincher stays at the water level on a right neighbourhood of every price while active; no absolute-continuity requirement on the paths; reason: event prices may accumulate (lumps of an admissible target can be dense) and, for an admissible AMM whose right marginal ask is flat on a fat Cantor set, the sole-survivor path X = Z(p) is continuous but not absolutely continuous, so a literal AC requirement would admit no run; on event-free intervals with AC paths the two formulations coincide
--   - encoding: a continuing run; Active, Clinch, b_i, h at the current price → p ∈ [p⋆, p_f); the sets and quantities after all events at p (Run.active, Run.clinch, Run.bud, Run.waterLevel); reason: the paper evaluates them after the event procedure at the current price
--   - generalization: reported values (v_i, q_i) ∈ ℝ²≥0 (the one-sided analysis of §4 allows only finite values, p.28) → values in WithTop ℝ, +∞ allowed (no hypothesis v_i ≠ ⊤); reason: values enter the mechanism only through exits, and the paper itself applies these structural lemmas to runs with infinite reports (proof of Lemma 6.2, p.28); on finite-value profiles the statement is the source's
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §4.4, Lemma 4.8, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_SybilClinch_IsRun
import Definitions.Def_SybilClinch_TargetMech_Admissible
import Definitions.Def_SybilClinch_OneSidedProfile_Valid
import Definitions.Def_SybilClinch_Run_alloc

set_option autoImplicit false

open Filter Topology Set MeasureTheory

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §4.4, Lemma 4.8 (Allocation structure and clincher persistence), printed p.18 (PDF p.20).

For every run of an admissible abstract target-based mechanism and every clock price `p` at which
the run continues (`p⋆ ≤ p < p_f`):
1. the supply invariant `S ≤ D₋ᵢ` (`i ∈ Active`) is equivalent to `bᵢ ≤ h` (`i ∈ Active`), and
   `{i ∈ Active : S = D₋ᵢ} = {i ∈ Active : bᵢ = h}` (39), where
   `D₋ᵢ = Σ_{j ≠ i, bⱼ > 0} bⱼ/p`;
2. an identity that has never clinched (through `p`) has received no allocation and made no
   payment;
3. once an identity clinches, it remains a clincher until the run ends;
4. no positive effective budget is exhausted: every identity with `vᵢ > p` and positive reported
   budget is active, and `bᵢ = min{qᵢ, h}` for `i ∈ Active` (40). -/
theorem lemma_4_8 (M : TargetMech) (hM : M.Admissible) (P : OneSidedProfile) (hP : P.Valid)
    (R : Run) (hR : IsRun M P R) (p : ℝ) (hp : p ∈ Ico M.pstar R.pf) :
    (((∀ i ∈ R.active M P p, R.resid M P p ≤
          (∑ j ∈ P.ids.filter (fun j => j ≠ i ∧ 0 < R.bud M P j p), R.bud M P j p) / p) ↔
        ∀ i ∈ R.active M P p, R.bud M P i p ≤ R.waterLevel M P p) ∧
      (R.active M P p).filter (fun i => R.resid M P p =
          (∑ j ∈ P.ids.filter (fun j => j ≠ i ∧ 0 < R.bud M P j p), R.bud M P j p) / p) =
        R.clinch M P p) ∧
    (∀ i ∈ P.ids, (∀ p' ∈ Icc M.pstar p, i ∉ R.clinch M P p') → R.x i p = 0 ∧ R.pay M i p = 0) ∧
    (∀ i, ∀ p₁ ∈ Icc M.pstar p, i ∈ R.clinch M P p₁ → i ∈ R.clinch M P p) ∧
    ((∀ i ∈ P.ids, (p : WithTop ℝ) < P.v i → 0 < P.q i → i ∈ R.active M P p) ∧
      ∀ i ∈ R.active M P p, R.bud M P i p = min (P.q i) (R.waterLevel M P p)) := by sorry

end SybilClinch
