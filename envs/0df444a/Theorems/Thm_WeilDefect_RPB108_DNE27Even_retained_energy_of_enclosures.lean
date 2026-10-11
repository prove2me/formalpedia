-- Prove2me | Theorems.Thm_WeilDefect_RPB108_DNE27Even_retained_energy_of_enclosures
-- name    : WeilDefect.RPB108.DNE27Even.retained_energy_of_enclosures
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T03:59:56.801669+00:00
-- url     : https://prove2.me/theorems/743a12a1-a10a-4ffe-9cb9-45de507eb2b9
-- title:
--   DNE27 even — Four-coordinate retained floor from native enclosures
-- statement:
--   For real matrices $A,V,G$ indexed by $\{0,1,2\}$ and complex coordinates $z$, write $Q_A(z)=\sum_{i,j}A_{ij}\operatorname{Re}(\overline{z_i}z_j)$, and for real coordinates $x$ write $R_A(x)=\sum_{i,j}A_{ij}x_ix_j$. For three off-diagonal bounds $u=(u_0,u_1,u_2)$, let $w_{01}=w_{10}=u_0$, $w_{02}=w_{20}=u_1$, $w_{12}=w_{21}=u_2$, and $w_{ii}=0$. Put $m(d,u)=(d_0-u_0-u_1,d_1-u_0-u_2,d_2-u_1-u_2)$. Use the unchanged exact even DNE27 rational data. Let $s_i$ denote the three retained column scales, $\rho$ the source/native Gram ratio, $d_i$ the scaled-difference diagonal lower entries, $u_i$ its off-diagonal bounds, and $\mu_i$ the published positive row margins. Let $R$ be the retained lower coefficient and $\theta$ the paid Young parameter. Write $V^-\le V\le V^+$ and $G^-\le G\le G^+$ for all nine entrywise lower/upper enclosure hypotheses, with no silent symmetry assumption. Assume all nine native-matrix interval bounds. For every $z\in\mathbb C^4$,
--
--   $$R\sum_{i=1}^3|z_i|^2\le Q_V((s_i z_{i+1})_{i=0}^2).$$
--
--   This reusable interface discharges the retained-energy hypothesis of the preceding conditional physical-gap theorem.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27RetainedEnergy.lean#L69-L73; exact native theorem WeilDefect.RPB108.DNE27Even.retained_energy_of_enclosures. SHA256 4a41ee4590c3cb7fb2d0ee15498dbafc45b1c6256b633b0d0bdb527587dd145b. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.

import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Even
import Definitions.Def_RPB108_DNE27RetainedEnergy_Even
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Even

theorem WeilDefect.RPB108.DNE27Even.retained_energy_of_enclosures (V : Fin 3 → Fin 3 → ℝ)
    (hV : ∀ i j, nativeLower i j ≤ V i j ∧ V i j ≤ nativeUpper i j)
    (z : Fin 4 → ℂ) :
    retainedEnergy z ≤ complexGram V (fun i => (gramScales i : ℂ)*z i.succ) := by sorry
