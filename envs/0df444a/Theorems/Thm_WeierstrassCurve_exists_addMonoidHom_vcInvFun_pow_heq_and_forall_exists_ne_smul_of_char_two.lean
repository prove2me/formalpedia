-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two
-- name    : WeierstrassCurve.exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/3af0bfa1-a0e5-5731-beab-cf60e340aace
-- title:
--   Automorphisms [ω], [i] of y²+y=x³ in characteristic two
-- statement:
--   Let $L$ be an algebraically closed field of characteristic $2$, let $w$ be a unit of $L$ with $w^3 = 1$ and $w \neq 1$, and let $M$ be a natural number whose image in $L$ is nonzero. Write $E_0$ for the Weierstrass curve with coefficients $(a_1,a_2,a_3,a_4,a_6) = (0,0,1,0,0)$, i.e. $y^2 + y = x^3$, and $E_0(L)$ for its group of affine points. Then there exist additive endomorphisms $\sigma$ and $\iota$ of $E_0(L)$ with the following properties. First, for every $k \in \mathbb{N}$ and every point $P$, the map `Point.vcInvFun` attached to the $k$-th power of the variable change $(u,r,s,t) = (w,0,0,0)$ — which sends $0$ to $0$ and $(x,y)$ to $(u^{-2}(x-r),\,u^{-3}(y-t-s(x-r)))$, viewed as a map to the points of the transformed curve — agrees, as a heterogeneous equality, with $\sigma^k(P)$; likewise the map attached to the $k$-th power of $(u,r,s,t) = (1,1,1,w)$ agrees with $\iota^k(P)$. Second, $\sigma(\sigma P) + \sigma P + P = 0$ and $\iota(\iota P) = -P$ for every $P$. Third, for each prime $p$ dividing $M$ there is a point $a$ of additive order exactly $p$ with $\sigma a \neq k \cdot a$ for all $k \in \mathbb{N}$, and, separately, a point $a$ of order exactly $p$ with $\iota a \neq k \cdot a$ for all $k \in \mathbb{N}$.
--
--   This packages the order-three and order-four automorphisms $[\omega]$ and $[i]$ of the supersingular curve $y^2+y=x^3$ in characteristic $2$ as group endomorphisms of its point group, records the relations $\sigma^2+\sigma+1=0$ and $\iota^2=-1$, and records that neither acts as a scalar on the $p$-torsion for any odd prime $p$ dividing $M$. It feeds the construction of torsion bases adapted to these automorphisms for curves of $j$-invariant $0$ and $1728$, and the transport statements built from them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] [CharP L 2]
    (w : Lˣ) (hw : (w : L) ^ 3 = 1) (hw1 : (w : L) ≠ 1) (M : ℕ) (hM : (M : L) ≠ 0) :
    ∃ σ ι : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point →+
        (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point,
      (∀ (k : ℕ) (P : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point),
        HEq (Point.vcInvFun ((⟨w, 0, 0, 0⟩ : VariableChange L) ^ k)
          (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine P) (σ^[k] P)) ∧
      (∀ (k : ℕ) (P : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point),
        HEq (Point.vcInvFun ((⟨1, 1, 1, (w : L)⟩ : VariableChange L) ^ k)
          (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine P) (ι^[k] P)) ∧
      (∀ P, σ (σ P) + σ P + P = 0) ∧ (∀ P, ι (ι P) = -P) ∧
      (∀ p : ℕ, p.Prime → p ∣ M →
        ∃ a : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point,
          addOrderOf a = p ∧ ∀ k : ℕ, σ a ≠ k • a) ∧
      (∀ p : ℕ, p.Prime → p ∣ M →
        ∃ a : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point,
          addOrderOf a = p ∧ ∀ k : ℕ, ι a ≠ k • a) := by sorry
