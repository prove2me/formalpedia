-- Prove2me | Theorems.Thm_SpatialSorting_coexistence_smooth_activities
-- name    : SpatialSorting.coexistence_smooth_activities
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:53:35.828084+00:00
-- url     : https://prove2.me/theorems/fdc489b4-d4ff-4dc7-8e38-07b5f00564f6
-- title:
--   Lemma 4.3 — coexistence, smooth activities and finite-object agreement
-- statement:
--   Fix $q\ge2$, bounds $0<a\le b$ for the off-diagonal costs and a smooth cutoff $\chi$. There is $\beta_0$ such that for every rate $c_*\in(0,a/64]$ (so $\tau_\beta=c_*\beta$, $\ell_0=1$), every $\beta\ge\beta_0$ and every cost matrix $A$ with $A_{\min}=a$, $A_{\max}=b$, the following hold on the field cube $\mathcal W_\beta=(-1,1)^q$.
--
--   1. For every colour $j$ and every contour $\gamma$ of type $j$, the auxiliary activity $\widehat w_j(\gamma;\cdot)$ is nonnegative on $\mathcal W_\beta$, translation invariant, and $C^2$ on $\mathcal W_\beta$, and for every coordinate $i$ and $k=0,1,2$,
--   $$\bigl|\partial^k_{h_i}\widehat w_j(\gamma;\mathbf h)\bigr|\le e^{-\tau_\beta|\overline\gamma|}\qquad(\mathbf h\in\mathcal W_\beta).\tag{20}$$
--   2. For every colour $j$ and $\mathbf h\in\mathcal W_\beta$, the box free energies $|Q_R|^{-1}\log\widehat Z_j(\beta,\mathbf h,Q_R)$ converge to the truncated pressure $\widehat\psi_j(\mathbf h)$ as $R\to\infty$ (the limit of Definition 3.3, Lemma B.1).
--   3. There is a field $\mathbf h^*_\beta\in\mathcal W_\beta$ with $h^*_0=0$ for which
--   $$\widehat\psi_0(\mathbf h^*_\beta)=\widehat\psi_1(\mathbf h^*_\beta)=\dots=\widehat\psi_{q-1}(\mathbf h^*_\beta),\qquad\|\mathbf h^*_\beta\|_\infty\le3qe^{-\tau_\beta\ell_0/4}.$$
--   4. Each fixed contour (of type $j$) has a neighbourhood of $\mathbf h^*_\beta$ on which its auxiliary activity agrees with the untruncated activity $w_j(\gamma)$; the same holds for the auxiliary and physical restricted partition functions $\widehat Z_j(V)$ and $Z^L_j(V)$ of each fixed finite region $V$ (which covers the ordinary regions with connected complement and the admissible restricted regions of Lemma 3.6). Consequently their values and first two coordinate derivatives agree at $\mathbf h^*_\beta$.
--
--   The lemma supplies the balanced field at which all phases coexist, together with uniform activity bounds that make the cluster expansion converge, while identifying the auxiliary objects with the physical ones exactly where they are used.
--
--   **Formalization Note** Coordinate derivatives are `iteratedDeriv k` of the restriction to the $i$-th coordinate line; agreement on a neighbourhood is `Filter.EventuallyEq` at $\mathbf h^*_\beta$; $\|\cdot\|_\infty$ is the sup norm of `Fin q → ℝ`. The page's closing sentence ("No common physical-agreement neighbourhood … is asserted") is a disclaimer and is not formalized.
--
--   Differences from the source:
--   - generalization: thresholds and constants that may depend on the cost matrix A ('for sufficiently large β'; Lemmas 4.3, 4.6, 6.1 print β0(q, A), C(q, A)), for the paper's one fixed cutoff χ → the constants are chosen from (q, A_min, A_max, χ) before the cost matrix, for every admissible cutoff χ; reason: every estimate of §§4–7 and Appendices A–C uses A only through A_min ≤ A(i, j) ≤ A_max for i ≠ j, and the paper's χ is one admissible cutoff, so the statement specializes to the printed one; Theorem 1 needs this uniformity
--   - generalization: τ_β = c*β with 0 < c* ≤ A_min/64 chosen sufficiently small, ℓ_0 = 1 → the bounds hold for every c* in (0, A_min/64], with the β-threshold independent of c*; reason: Appendix C proves every displayed decay bound at the concrete rate βA_min/64 (p.57, PDF p.58), and each bound of the lemma weakens as c* decreases, so every admissible choice of c* is covered; ℓ_0 = 1 as on p.24
--   - generalization: Definition 3.3 defines ψ̂_j as a limit whose existence is proved in Lemma B.1 → adds the convergence of the box free energies to ψ̂_j at every field of the cube; reason: Lemma B.1 proves it under the bounds (20); stating it rules out a balance between default values of an undefined limit
--   - encoding: agreement 'on a neighborhood' of h*_β for each fixed contour and region → Filter.EventuallyEq at 𝓝 h*_β, for every type-j contour and every finite region V, with Z^L_j as the physical restricted partition function; reason: Lemma 3.6 identifies Z^L_j(V) with the physical polymer sum; on a region with connected complement it is the ordinary partition function (Definition 3.5)
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 4.3, p. 25 (PDF p. 26)

import Mathlib
import Definitions.Def_SpatialSorting_D
import Definitions.Def_SpatialSorting_IsCostMatrix
import Definitions.Def_SpatialSorting_amin
import Definitions.Def_SpatialSorting_amax
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_IsContour
import Definitions.Def_SpatialSorting_translate
import Definitions.Def_SpatialSorting_IsType
import Definitions.Def_SpatialSorting_Zres
import Definitions.Def_SpatialSorting_w
import Definitions.Def_SpatialSorting_IsCutoff
import Definitions.Def_SpatialSorting_what
import Definitions.Def_SpatialSorting_Zhat
import Definitions.Def_SpatialSorting_pressure
import Definitions.Def_SpatialSorting_IsCoexistenceField
open Classical Filter Topology

namespace SpatialSorting

/-- Lemma 4.3 — coexistence, smooth activities and finite-object agreement.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 4.3, p. 25 (PDF p. 26).

Formalization Notes:
- generalization: thresholds and constants that may depend on the cost matrix A ('for sufficiently large β'; Lemmas 4.3, 4.6, 6.1 print β0(q, A), C(q, A)), for the paper's one fixed cutoff χ → the constants are chosen from (q, A_min, A_max, χ) before the cost matrix, for every admissible cutoff χ. Every estimate of §§4–7 and Appendices A–C uses A only through A_min ≤ A(i, j) ≤ A_max for i ≠ j, and the paper's χ is one admissible cutoff, so the statement specializes to the printed one; Theorem 1 needs this uniformity.
- generalization: τ_β = c*β with 0 < c* ≤ A_min/64 chosen sufficiently small, ℓ_0 = 1 → the bounds hold for every c* in (0, A_min/64], with the β-threshold independent of c*. Appendix C proves every displayed decay bound at the concrete rate βA_min/64 (p.57, PDF p.58), and each bound of the lemma weakens as c* decreases, so every admissible choice of c* is covered; ℓ_0 = 1 as on p.24.
- generalization: Definition 3.3 defines ψ̂_j as a limit whose existence is proved in Lemma B.1 → adds the convergence of the box free energies to ψ̂_j at every field of the cube. Lemma B.1 proves it under the bounds (20); stating it rules out a balance between default values of an undefined limit.
- encoding: agreement 'on a neighborhood' of h*_β for each fixed contour and region → Filter.EventuallyEq at 𝓝 h*_β, for every type-j contour and every finite region V, with Z^L_j as the physical restricted partition function. Lemma 3.6 identifies Z^L_j(V) with the physical polymer sum; on a region with connected complement it is the ordinary partition function (Definition 3.5). -/
theorem coexistence_smooth_activities :
    ∀ (q : ℕ) [NeZero q], 2 ≤ q → ∀ a b : ℝ, 0 < a → a ≤ b →
      ∀ χ : ℝ → ℝ, IsCutoff χ →
        ∃ β0 : ℝ, ∀ cstar : ℝ, 0 < cstar → cstar ≤ a / 64 → ∀ β : ℝ, β0 ≤ β →
          ∀ A : Matrix (Fin q) (Fin q) ℝ, IsCostMatrix A → amin A = a → amax A = b →
            let cube : Set (Fin q → ℝ) := Set.pi Set.univ (fun _ => Set.Ioo (-1 : ℝ) 1)
            (∀ (j : Fin q) (γ : Contour q), IsContour γ → IsType j γ →
              (∀ h ∈ cube, 0 ≤ what A χ β j γ h) ∧
              (∀ (v : ℤ × ℤ) (h : Fin q → ℝ), what A χ β j (translate γ v) h = what A χ β j γ h) ∧
              ContDiffOn ℝ 2 (what A χ β j γ) cube ∧
              ∀ h ∈ cube, ∀ (i : Fin q) (k : ℕ), k ≤ 2 →
                |iteratedDeriv k (fun t => what A χ β j γ (Function.update h i t)) (h i)| ≤
                  Real.exp (-(cstar * β) * (γ.support.card : ℝ))) ∧
            (∀ (j : Fin q), ∀ h ∈ cube,
              Tendsto (fun R : ℕ => ((D R).card : ℝ)⁻¹ * Real.log (Zhat A χ β j (D R) h)) atTop
                (𝓝 (pressure A χ β j h))) ∧
            ∃ hs : Fin q → ℝ, IsCoexistenceField A χ β hs ∧
              ‖hs‖ ≤ 3 * (q : ℝ) * Real.exp (-(cstar * β) / 4) ∧
              (∀ (j : Fin q) (γ : Contour q), IsContour γ → IsType j γ →
                (what A χ β j γ =ᶠ[𝓝 hs] fun h => w A β h j γ) ∧
                ∀ (i : Fin q) (k : ℕ), k ≤ 2 →
                  iteratedDeriv k (fun t => what A χ β j γ (Function.update hs i t)) (hs i) =
                    iteratedDeriv k (fun t => w A β (Function.update hs i t) j γ) (hs i)) ∧
              ∀ (j : Fin q) (V : Finset (ℤ × ℤ)),
                (Zhat A χ β j V =ᶠ[𝓝 hs] fun h => Zres A β h j V) ∧
                ∀ (i : Fin q) (k : ℕ), k ≤ 2 →
                  iteratedDeriv k (fun t => Zhat A χ β j V (Function.update hs i t)) (hs i) =
                    iteratedDeriv k (fun t => Zres A β (Function.update hs i t) j V) (hs i) := by sorry

end SpatialSorting
