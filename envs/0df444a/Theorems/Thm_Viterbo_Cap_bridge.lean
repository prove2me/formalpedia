-- Prove2me | Theorems.Thm_Viterbo_Cap_bridge
-- name    : Viterbo.Cap.bridge
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T17:50:21.75569+00:00
-- url     : https://prove2.me/theorems/d5b24c05-d791-4c76-bca0-2053693d5717
-- title:
--   From a symplectic embedding of convex domains to centred data in ℂⁿ — a smooth symplectic open embedding e with e(0) = 0 and gauge_{L'} ∘ e ≤ θ < 1, L' a (1+η)-enlargement of L
-- statement:
--   Let $n\ge1$, $K,L\subseteq\mathbb R^{2n}$ convex domains with `HasSymplecticEmbedding K L`, and $\eta>0$. Then there are $K',L'\subseteq\mathbb C^n$, $r$, and a partial homeomorphism $e$ of $\mathbb C^n$ (`OpenPartialHomeomorph`) such that, writing $\Psi(w)=(\operatorname{Re}w,\operatorname{Im}w)$:
--   - `Body K' r`, $\Psi(K')$ is a convex domain and $c_{\rm EHZ}(\Psi(K'))=c_{\rm EHZ}(K)$;
--   - $\Psi(L')$ is a convex domain with $0$ in its interior and $c_{\rm EHZ}(\Psi(L'))=(1+\eta)^2c_{\rm EHZ}(L)$;
--   - the source of $e$ is the interior of $K'$, contains $0$, $e(0)=0$, $e$ is $C^\infty$ on its source and its derivative at every source point preserves the form `OAI.ComplexSymplectic.form`;
--   - for some $\theta<1$, $\operatorname{gauge}_{L'}(e(w))\le\theta$ for every $w$ in the source.
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), p. 2, a step in the proof of the capacity statement (Hofer–Zehnder argument, Hofer, H. and Zehnder, E., Symplectic Invariants and Hamiltonian Dynamics, Birkhäuser (1994), https://doi.org/10.1007/978-3-0348-8540-9, ch. 3)

import Mathlib
import Definitions.Def_Viterbo
import Definitions.Def_ViterboCap

open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic

namespace Viterbo.Cap

theorem bridge {n : ℕ} (hn : 1 ≤ n) {K L : Set (Phase n)} (hK : IsConvexDomain K)
    (hL : IsConvexDomain L) (he : HasSymplecticEmbedding K L) {η : ℝ} (hη : 0 < η) :
    ∃ (K' L' : Set (Vector (Fin n))) (r : ℝ) (e : OpenPartialHomeomorph (Vector (Fin n)) (Vector (Fin n))),
      Body K' r ∧ IsConvexDomain (Capacities.Ψ n '' K') ∧
      cEHZ (Capacities.Ψ n '' K') = cEHZ K ∧
      IsConvexDomain (Capacities.Ψ n '' L') ∧ (0 : Phase n) ∈ interior (Capacities.Ψ n '' L') ∧
      cEHZ (Capacities.Ψ n '' L') = ENNReal.ofReal ((1 + η) ^ 2) * cEHZ L ∧
      e.source = interior K' ∧ (0 : Vector (Fin n)) ∈ e.source ∧ e 0 = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧
      (∀ w ∈ e.source, OAI.ComplexSymplectic.Preserves (fderiv ℝ e w)) ∧
      ∃ θ : ℝ, θ < 1 ∧ ∀ w ∈ e.source, gauge L' (e w) ≤ θ := by
  sorry

end Viterbo.Cap
