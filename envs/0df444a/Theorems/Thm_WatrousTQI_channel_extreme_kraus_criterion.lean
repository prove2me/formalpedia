-- Prove2me | Theorems.Thm_WatrousTQI_channel_extreme_kraus_criterion
-- name    : WatrousTQI.channel_extreme_kraus_criterion
-- status  : Open
-- author  : @Mrnaiq
-- created : 2026-11-12T22:36:03.883445+00:00
-- url     : https://prove2.me/theorems/898e0144-5902-4228-bb76-63c1e78936d6
-- title:
--   Theorem 2.31 — Choi’s characterization of extreme quantum channels
-- statement:
--   Let $\Phi:M_{d_X}(\mathbb C)\to M_{d_Y}(\mathbb C)$ be a quantum channel on arbitrary positive finite dimensions. Suppose $A_0,\ldots,A_{m-1}$ form a complex-linearly independent Kraus representation of $\Phi$ on every input matrix. Then $$\Phi\in\operatorname{ext}_{\mathbb R}\mathcal C(d_X,d_Y)\quad\Longleftrightarrow\quad(A_b^\dagger A_a)_{a,b}\text{ is linearly independent over }\mathbb C.$$ The convex set is the entire set of trace-preserving completely positive maps between these spaces. It is not restricted to unital, square, classical-to-quantum, or rank-one Kraus maps. Channels reuse the published finite-normalized-Kraus predicate.
-- source:
--   John Watrous, The Theory of Quantum Information, Cambridge University Press, 2018, Section 2.2.4, printed pp.96–99. https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf; Theorem 2.31, equations (2.174)–(2.175), printed pp.97–99.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder BigOperators

namespace WatrousTQI
theorem channel_extreme_kraus_criterion {dx dy m : ℕ}
    (hdx : 0 < dx) (hdy : 0 < dy) (hm : 0 < m)
    (Φ : QAlgorithms.Superop (Fin dx) (Fin dy))
    (hΦ : QAlgorithms.IsChannel Φ)
    (A : Fin m → Matrix (Fin dy) (Fin dx) ℂ)
    (hLI : LinearIndependent ℂ A)
    (hrep : ∀ X, Φ X = QAlgorithms.krausApply A X) :
    Φ ∈ ({Ψ : QAlgorithms.Superop (Fin dx) (Fin dy) | QAlgorithms.IsChannel Ψ}).extremePoints ℝ ↔
      LinearIndependent ℂ (fun ab : Fin m × Fin m => (A ab.2)ᴴ * A ab.1) := by sorry
end WatrousTQI
