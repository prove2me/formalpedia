-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_variableChange_tateCurve_algebraicClosure_galois_signBehavior
-- name    : WeierstrassCurve.exists_variableChange_tateCurve_algebraicClosure_galois_signBehavior
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/7fc42214-e1dc-5da8-8116-464d6feea331
-- title:
--   Galois sign behaviour of the Tate curve variable change
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ and $p$ a prime, and assume $\Delta(W)\neq 0$, $p \mid \Delta(W)$ and $p \nmid c_4(W)$. Let $q_T \in \mathbb{Q}_p$ satisfy $q_T \neq 0$ and $\lVert q_T\rVert < 1$, and write $E_{q_T}$ for the Tate curve [`TateCurve.curve`](def/TateCurve_QSeries.html#L185) $q_T$, i.e. the Weierstrass curve $\langle 1,0,0,a_4(q_T),a_6(q_T)\rangle$ with the $q$-series coefficients $a_4,a_6$. Assume the invariants are matched in the form $c_4(E_{q_T})^3 = \iota_p\!\left(c_4(W_{\mathbb{Q}})^3/\Delta(W_{\mathbb{Q}})\right)\cdot \Delta(E_{q_T})$, where $W_{\mathbb{Q}}$ is $W$ base-changed to $\mathbb{Q}$ and $\iota_p$ is the inclusion $\mathbb{Q}\hookrightarrow\mathbb{Q}_p$. The conclusion asserts the existence of $d\in\mathbb{Q}_p$ with $\lVert d\rVert = 1$, of $s$ in $\overline{\mathbb{Q}_p} =$ `AlgebraicClosure` $\mathbb{Q}_p$ with $s^2 = d$, and of a Weierstrass variable change $C$ over $\overline{\mathbb{Q}_p}$ such that $C \bullet W_{\overline{\mathbb{Q}_p}} = (E_{q_T})_{\overline{\mathbb{Q}_p}}$ (both curves base-changed from $\mathbb{Z}$, resp. $\mathbb{Q}_p$), and such that for every $\sigma \in \mathrm{Aut}_{\mathbb{Q}_p}(\overline{\mathbb{Q}_p})$ the entrywise image $\sigma(C)$ equals $C$ when $\sigma s = s$, and equals $\langle -1,0,-1,0\rangle \cdot C$ when $\sigma s \neq s$.
--
--   This is the variable-change level statement that the Frey curve $W$, having multiplicative reduction at $p$ and matching invariants, becomes isomorphic over $\overline{\mathbb{Q}_p}$ to the Tate curve $E_{q_T}$ by an isomorphism defined over the quadratic extension $\mathbb{Q}_p(s)$, with Galois cocycle given exactly by the quadratic character of $d$ and the automorphism $\langle -1,0,-1,0\rangle = [-1]$ of $E_{q_T}$. It feeds the comparison of $p$-torsion modules of $W$ and of a sign twist of the Tate curve in [`WeierstrassCurve.exists_addEquiv_torsion_tateCurve_signTwist_of_tateParameter`](thm.html#WeierstrassCurve.exists_addEquiv_torsion_tateCurve_signTwist_of_tateParameter).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_variableChange_tateCurve_algebraicClosure_galois_signBehavior.lean

import Mathlib
import Definitions.Def_TateCurve_TateParameter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal
open scoped WeierstrassCurve.Affine in
open WeierstrassCurve in

theorem WeierstrassCurve.exists_variableChange_tateCurve_algebraicClosure_galois_signBehavior
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hΔ : W.Δ ≠ 0)
    (hpΔ : (p : ℤ) ∣ W.Δ) (hpc₄ : ¬ (p : ℤ) ∣ W.c₄)
    (qT : ℚ_[p]) (hqT0 : qT ≠ 0) (hqT1 : ‖qT‖₊ < 1)
    (hj : (TateCurve.curve qT).c₄ ^ 3
        = (((W.map (Int.castRingHom ℚ)).c₄ ^ 3 / (W.map (Int.castRingHom ℚ)).Δ : ℚ) : ℚ_[p])
            * (TateCurve.curve qT).Δ) :
    ∃ (d : ℚ_[p]), ‖d‖₊ = 1 ∧
      ∃ (s : AlgebraicClosure ℚ_[p]), s ^ 2 = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) d ∧
        ∃ C : VariableChange (AlgebraicClosure ℚ_[p]),
          C • ((W.map (Int.castRingHom ℚ_[p])).map (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])))
            = (TateCurve.curve qT).map (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])) ∧
          ∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
            (σ s = s → C.map σ.toAlgHom.toRingHom = C) ∧
            (σ s ≠ s → C.map σ.toAlgHom.toRingHom
              = (⟨-1, 0, -1, 0⟩ : VariableChange (AlgebraicClosure ℚ_[p])) * C) := by sorry
