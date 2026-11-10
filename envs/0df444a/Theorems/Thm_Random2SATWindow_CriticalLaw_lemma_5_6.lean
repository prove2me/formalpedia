-- Prove2me | Theorems.Thm_Random2SATWindow_CriticalLaw_lemma_5_6
-- name    : Random2SATWindow.CriticalLaw.lemma_5_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:42:20.107368+00:00
-- url     : https://prove2.me/theorems/988fb0ad-bc5c-41a3-a879-65c89f5d8d2d
-- title:
--   Lemma 5.6 — on satisfiable formulas $R(F)\le X(F)$
-- statement:
--   On satisfiable formulas, $R(F)\le X(F)$, where $R(F)$ is the physical SCC excess (6) and $X(F)=m_C-b_C$ the excess of the pure literal core (128).
--
--   Differences from the source:
--   - encoding: F_C, the clauses left by the pure literal algorithm → pureCore F, the largest subformula in which every occurring variable has both polarities; reason: the paper proves the two are equal (printed p. 50)
--   - encoding: R(F) = ½ Σ_{C ∈ SCC(D(F))} r(C) for F ∈ SAT (6) → physExcess F = (Σ_C r(C)) / 2 in ℕ, used only together with Satisfiable F; reason: on SAT the SCCs come in mirror pairs of equal excess, so the sum is even and the halving is exact
--   - encoding: 2-SAT formulas: sets of distinct legal clauses on two distinct variables; F(n, p) independent clauses, F(n, m) uniform m-subsets of the N_n = 2n(n−1) legal clauses → LegalClause n = unordered pairs (Sym2) of literals Fin n × Bool whose variables differ, Formula n = Finset (LegalClause n); probBinom n p E = Σ_{F ∈ E} p^{|F|}(1−p)^{N_n−|F|}, satProbUniform n m = #{F : |F| = m, F ∈ SAT}/C(N_n, m); reason: the paper's model verbatim; N_n = Fintype.card (LegalClause n) = 2n(n−1)
-- source:
--   Ravelomanana, Inside the Critical Window of Random 2-SAT, STOC 2027 submission (manuscript sha256 eef2fa67…), Lemma 5.6, printed p. 50 (PDF 52); proof printed p. 51 (PDF 53)

import Mathlib
import Definitions.Def_Random2SATWindow_CriticalLaw_Formulas
import Definitions.Def_Random2SATWindow_CriticalLaw_Airy
import Definitions.Def_Random2SATWindow_CriticalLaw_Hadamard
import Definitions.Def_Random2SATWindow_CriticalLaw_Strata
import Definitions.Def_Random2SATWindow_CriticalLaw_Saddle
import Definitions.Def_Random2SATWindow_CriticalLaw_PureLiteral

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace Random2SATWindow.CriticalLaw

/-- **Lemma 5.6** (printed p. 50 / PDF 52; proof printed p. 51 / PDF 53). On satisfiable
formulas, `R(F) ≤ X(F)`: the physical SCC excess is at most the excess of the pure literal core. -/
theorem lemma_5_6 {n : ℕ} (F : Formula n) (hF : Satisfiable F) :
    (physExcess F : ℤ) ≤ coreExcess F := by sorry

end Random2SATWindow.CriticalLaw
