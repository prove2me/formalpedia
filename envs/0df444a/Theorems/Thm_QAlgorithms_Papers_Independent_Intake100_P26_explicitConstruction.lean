-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P26_explicitConstruction
-- name    : QAlgorithms.Papers.Independent.Intake100.P26.explicitConstruction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:24:21.698235+00:00
-- url     : https://prove2.me/theorems/72ea92ca-b9f2-4434-b0a7-3a947710cd8b
-- title:
--   The explicit irreducible seminormal module
-- statement:
--   Let $R$ be a finite reduced irreducible crystallographic root system of positive rank, with a fixed positive system and simple roots $\alpha_i$, Weyl group $W$, and full weight lattice $P$. Fix $q\in\mathbb C^\times$ which is not a root of unity. Write $\widetilde H$ for its affine Hecke algebra with $T_i^2=(q-q^{-1})T_i+1$ and the Bernstein relation with denominator $1-X^{-\alpha_i}$ interpreted as a Laurent-polynomial divided difference. Let $T=\operatorname{Hom}(P,\mathbb C^\times)$, with $(wt)(X^\lambda)=t(X^{w^{-1}\lambda})$. All modules below are finite dimensional complex left modules. Irreducible modules are nonzero.
--
--   For $t\in T$, set $Z(t)=\{\alpha>0:t(X^\alpha)=1\}$ and $P_q(t)=\{\alpha>0:t(X^\alpha)=q^{\pm2}\}$. Let $(t,J)$ be a placed skew shape: $J\subseteq P_q(t)$, the set $F(t,J)=\{w:R(w)\cap Z(t)=\varnothing,\ R(w)\cap P_q(t)=J\}$ is nonempty, and each $wt$ in this set is simple-root regular and rank-two calibratable as specified in §3. Here $R(w)=\{\alpha>0:w\alpha<0\}$.
--
--   Here rank-two calibratability means either every root of the generated subsystem evaluates differently from $1$, or the subsystem has type $C_2$ or $G_2$ and some element of its rank-two Weyl group moves the character to values $q^2$ on the long simple root and $1$ on the short simple root, with both original simple-root evaluations different from $1$.
--
--   On the free complex vector space with basis $v_w$, $w\in F(t,J)$, define
--   $$X^\lambda v_w=(wt)(X^\lambda)v_w,\qquad T_i v_w=\frac{q-q^{-1}}{1-(wt)(X^{-\alpha_i})}v_w+\left(q^{-1}+\frac{q-q^{-1}}{1-(wt)(X^{-\alpha_i})}\right)v_{s_iw},$$
--   where $v_{s_iw}=0$ outside $F(t,J)$. These operators satisfy the affine Hecke relations and give an irreducible calibrated module of dimension $|F(t,J)|$.
--
--   This is an explicit construction on a specified basis. The simple-root regularity condition repairs the rank-one omission in the printed shape definition, following the denominator requirement used in the proof.
-- source:
--   Calibrated representations of affine Hecke algebras, arXiv:math/0401323v2, PDF p. 12, Theorem 3.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P26

open scoped BigOperators

variable {D : Datum} {V U : Type*}

variable [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]

/-- Theorem 3.1, PDF p.12 (proof pp.12--14). The operator formulas are
constructed in `tableauGenerators`; relation satisfaction and nonzero calibrated
irreducibility are conclusions. Rank-one regularity is repaired in the
shape definition, following the proof's explicit denominator requirement. -/
theorem explicitConstruction (D : Datum) (q : ℂ) (hq : GoodParameter q)
    (t : Torus D) (J : Set (Fin D.rootCount)) (hshape : PlacedSkewShape D q t J) :
    Relations q (tableauGenerators D q t J) ∧
    HeckeIrreducible (tableauGenerators D q t J) ∧ Calibrated (tableauGenerators D q t J) ∧
    Module.finrank ℂ (TableauSpace D q t J) =
      Nat.card {w : Weyl D // w ∈ tableaux D q t J} := by sorry

end QAlgorithms.Papers.Independent.Intake100.P26

end
