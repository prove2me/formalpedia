-- Prove2me | Theorems.Thm_SingleMachinePrec_IntervalReduction_light_weight
-- name    : SingleMachinePrec.IntervalReduction.light_weight
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:32:07.940253+00:00
-- url     : https://prove2.me/theorems/9967b9ce-2e3a-40db-bb50-2ccdfe603c08
-- title:
--   §7, p. 664 — the light nodes weigh less than 1 in total, so $w(C'_I) = \lfloor w(C_I)\rfloor$
-- statement:
--   Let $S$ be the Stage 2 instance, with $n$ jobs and $k=n^2+1$. Let $w(C_I)$ be the minimum weight of a vertex cover of $G^S_I$ and $w(C'_I)=|C'_I|$ the minimum size of a vertex cover of the unweighted graph $G'_I$ induced by $D$. Then
--   $$\sum_{(i,j)\in\operatorname{inc}(I)\setminus D} p_i w_j < 1 \qquad\text{and}\qquad w(C'_I)=\lfloor w(C_I)\rfloor.$$
--
--   The weight-one nodes thus determine the optimum exactly, up to the fractional contribution of the light nodes, which the floor removes.
--
--   **Formalization Note** $\lfloor\cdot\rfloor$ is `Nat.floor`, which equals the integer floor here because $w(C_I)\ge 0$. The left sum ranges over all ordered incomparable pairs of $I$ that are not in $D$.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 664, §7 (display following the choice k = n^2 + 1)

import Mathlib
import Definitions.Def_SingleMachinePrec_IntervalReduction_Instance

namespace SingleMachinePrec.IntervalReduction

open Classical in
/-- §7, p. 664: with `k = n² + 1`, the incomparable pairs outside `D` have total weight
`∑_{(i,j) ∈ inc(I) \ D} p_i w_j < 1`, and therefore the minimum vertex cover of the unweighted
graph `G′_I` has size `⌊w(C_I)⌋`. -/
theorem light_weight {N : ℕ} {G : SimpleGraph (Fin N)} (L : TreeLayout G) :
    (∑ u : IncPair (prec L),
        if InD L u.1.1 u.1.2 then 0
        else vertexWeight (prec L) (procTime L (kVal L)) (weight L (kVal L)) u) < 1 ∧
    (GIprime L).vertexCoverNum = ((⌊tauW L⌋₊ : ℕ) : ℕ∞) := by sorry

end SingleMachinePrec.IntervalReduction
