-- Prove2me | Theorems.Thm_V3Glue_ChartInput_comap_iotaY_compG_chainPosPrime_eq
-- name    : V3Glue.ChartInput.comap_iotaY_compG_chainPosPrime_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/f59507f1-c60d-58ea-8613-73ba9a654d3f
-- title:
--   Glued components restrict to pullbacks of the model labels
-- statement:
--   Let $X$ be a scheme and $N$ a type, and let $C$ be a chart input on $X$ indexed by $N$ (so $C$ provides marked points $x_n$, the open complement $X_0$ of all of them, charts $f_n \colon U_n \to S_n$, proper modifications $\rho_n \colon \mathrm{Res}_n \to S_n$ that are isomorphisms over $V^{\mathrm c}_n$, thicknesses $\mathrm{thick}(n) \ge 1$, and the auxiliary data $Y_n$, $q_n$, $j_n$, $g_n$ over the base $B$). Assume: for every $n$ the residue field map of $f_n$ at the marked point of $U_n$ is an isomorphism (`hRF`); points $\mathrm{gRes}(n,k)$ of $\mathrm{Res}_n$, indexed by $k \in \mathrm{Fin}(\mathrm{thick}(n)-1)$, all lying over the vertex $(f_n)(x_n) \in S_n$; two points $\xi_0, \xi_1 \in X_0$. Fix $n \in N$ and a family $F_0, \dots, F_{\mathrm{thick}(n)}$ of ideal sheaf data on $\mathrm{Res}_n$ such that for each $k$, $F_{k+1}$ is the vanishing ideal of the closure of $\{\mathrm{gRes}(n,k)\}$ and the pullback of $g_n$ along the closed immersion cut out by $F_{k+1}$ is reduced; assume further $\xi_j \in U_n$ for $j \in \mathrm{Fin}\,2$, points $\lambda_0, \lambda_1 \in \mathrm{Res}_n$ with the support of $F_0$ (resp. $F_{\mathrm{thick}(n)}$) equal as a set to the closure of $\{\lambda_0\}$ (resp. $\{\lambda_1\}$), the corresponding pullbacks along the two end subschemes again reduced, and the fibre of $(g_n)$ over $\lambda_j$ equal to the single point $C.\xi Y$ associated with $\xi_j$. Then for every $d \in \mathrm{Fin}(\mathrm{thick}(n)+1)$ the comap along the canonical morphism $Y_n \to$ (glued scheme) of the component ideal sheaf $\mathrm{compG}$ at the chain position $\mathrm{chainPos}'(n,d)$ — which is $\mathrm{Sum.inl}\,0$ for $d = 0$, $\mathrm{Sum.inr}\,(n,d-1)$ for $0 < d < \mathrm{thick}(n)$, and $\mathrm{Sum.inl}\,1$ otherwise, and whose value is the vanishing ideal of the closure of the corresponding point $\eta G$ of the glued scheme — coincides with the comap of $F_d$ along $g_n$.
--
--   This is the chart-wise identification of the irreducible components of the glued scheme, restricted to a single chart, with the prescribed label family on the model resolution: the exceptional positions match the vanishing ideals of the exceptional points, and the two extreme positions the ideals supported on the strict branches. It supplies the label compatibility used in the assembly of the resolved model, and is invoked by the statements about component products and labels in that assembly.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_V3Glue_ChartInput_comap_iotaY_compG_chainPosPrime_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ResolvedModelGlueComponents

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem V3Glue.ChartInput.comap_iotaY_compG_chainPosPrime_eq {X : Scheme.{0}} {N : Type} (C : V3Glue.ChartInput X N)
    (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
    (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
    (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0) (n : N)
    (F : Fin (C.thick n + 1) → (C.Res n).IdealSheafData)

    (hFexc : ∀ k : Fin (C.thick n - 1), F ⟨(k : ℕ) + 1, by omega⟩ =
      Scheme.IdealSheafData.vanishingIdeal ⟨closure {gRes n k}, isClosed_closure⟩)
    (hred : ∀ k : Fin (C.thick n - 1), IsReduced (pullback (C.g n) (F ⟨(k : ℕ) + 1, by omega⟩).subschemeι))

    (hU : ∀ j : Fin 2, ξ j ∈ C.U n) (lam : Fin 2 → C.Res n)
    (hFend : ∀ j : Fin 2, ((F (Fin.cases 0 (fun _ => Fin.last _) j)).support : Set (C.Res n)) = closure {lam j})
    (hredEnd : ∀ j : Fin 2, IsReduced (pullback (C.g n) (F (Fin.cases 0 (fun _ => Fin.last _) j)).subschemeι))
    (hlam : ∀ j : Fin 2, (C.g n).base ⁻¹' {lam j} = {C.ξY ξ hξ n j (hU j)}) (d : Fin (C.thick n + 1)) :
    (C.compG hRF gRes hgRes ξ hξ (C.chainPos' n d)).comap (C.toGlueInput.ιY n) = (F d).comap (C.g n) := by sorry
