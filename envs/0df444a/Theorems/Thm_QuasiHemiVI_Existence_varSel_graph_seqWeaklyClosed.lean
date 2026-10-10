-- Prove2me | Theorems.Thm_QuasiHemiVI_Existence_varSel_graph_seqWeaklyClosed
-- name    : QuasiHemiVI.Existence.varSel_graph_seqWeaklyClosed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:35:25.630397+00:00
-- url     : https://prove2.me/theorems/63ab8c1a-5d76-4ab5-add2-c26fb192f259
-- title:
--   Proof of Theorem 3.8 (ii) — the graph of the variational selection $S$ is sequentially weakly closed
-- statement:
--   Let $V$ be a real reflexive Banach space and $X$, $Y$ real Banach spaces, and assume all hypotheses of Theorem 3.8: (HC), (HJ), (Hγ), (H0), (HT) with $h$ convex, (Hφ), (HK), (HC0), $\gamma$ compact, and (3.19). For $w\in C$ let $S(w)$ be the set of $u\in K(w)$ for which some $u^*\in T(u)$ satisfies
--
--   $$
--   \langle u^*,v-u\rangle+\varphi(v,u)+J^0(\gamma u;\gamma(v-u))\ge\langle f,\pi(v-u)\rangle_{Y^*\times Y}\quad\text{for all }v\in K(w).\qquad(3.21)
--   $$
--
--   Then the graph of $S:C\to2^C$ is sequentially weakly closed: if $u_n\in S(w_n)$ with $w_n\rightharpoonup w$ and $u_n\rightharpoonup u$ in $V$, for some $w,u\in C$, then $u\in S(w)$.
--
--   This is one of the hypotheses of Kluge's fixed point theorem (Theorem 2.7) for $S$ and is the step where the compactness of $\gamma$, the Mosco-type conditions (HK) and condition (3.19) are used.
-- source:
--   Zeng, Migórski & Khan, Nonlinear Quasi-hemivariational Inequalities: Existence and Optimal Control, SIAM J. Control Optim. 59(2) (2021) 1246–1274, doi:10.1137/19M1282210, pp. 1259–1260, proof of Theorem 3.8 (ii): "We claim that the graph of variational selection S is sequentially weakly closed."

import Mathlib
import Definitions.Def_QuasiHemiVI_Existence_ClarkeDeriv
import Definitions.Def_QuasiHemiVI_Existence_WeakConv
import Definitions.Def_QuasiHemiVI_Existence_SetValued
import Definitions.Def_QuasiHemiVI_Existence_Hypotheses
import Definitions.Def_QuasiHemiVI_Existence_Problems

namespace QuasiHemiVI.Existence

/-- Proof of Theorem 3.8 (ii), pp. 1259–1260: under the hypotheses of Theorem 3.8, the graph of
the variational selection `S` (`S(w)` = solutions in `K(w)` of (3.21)) is sequentially weakly
closed in `C × C`. -/
theorem varSel_graph_seqWeaklyClosed {V X Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (hV : IsReflexive V)
    (C : Set V) (K : V → Set V) (T : V → Set (V →L[ℝ] ℝ)) (φ : V → V → ℝ) (J : X → ℝ)
    (γ : V →L[ℝ] X) (π : V →L[ℝ] Y) (f : Y →L[ℝ] ℝ) (h : V → ℝ) (C₀ : Set V)
    (hC : HC C) (hJ : LocallyLipschitz J) (hT : HT C T φ J γ π f h)
    (hhcvx : ConvexOn ℝ Set.univ h) (hφ : Hphi φ) (hK : HK C K) (hC0 : HC0 C K T φ J γ C₀)
    (hγ : IsCompactOperator γ) (h319 : Cond319 C φ) :
    SeqWeaklyClosedGraphOn C (varSel K T φ J γ π f) := by sorry

end QuasiHemiVI.Existence
