-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P50_j2_basis_coefficient_criterion
-- name    : QAlgorithms.Papers.Independent.Dependency50.P50.j2_basis_coefficient_criterion
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:27:08.427859+00:00
-- url     : https://prove2.me/theorems/df2a0a16-e8cb-4e5e-9ec4-aed76eae55d7
-- title:
--   Coefficient criterion and explicit witness for J2 basis dependence
-- statement:
--   Let $n,m>0$ and let $(F_a)_{a\in\{1,\ldots,n\}^2}$ be any complex basis of $M_n(\mathbb C)$. For canonical matrix units $E_{kl}$, put $c_{a,kl}=\langle F_a,E_{kl}\rangle_{\rm HS}=(F_a)_{kl}$, where the Hilbert–Schmidt pairing is linear in its first argument. For every complex-linear $T:M_n(\mathbb C)\to M_m(\mathbb C)$ define $J_{2,F}(T)=\sum_a F_a\otimes T(F_a)$ and $J_2(T)=\sum_{kl}E_{kl}\otimes T(E_{kl})$. Then
--
--   $$J_{2,F}(T)=\sum_{k,l,p,q}\left(\sum_a c_{a,kl}c_{a,pq}\right)E_{kl}\otimes T(E_{pq}),$$
--
--   and
--
--   $$\bigl(\forall T,\ J_{2,F}(T)=J_2(T)\bigr)\iff\bigl(\forall k,l,p,q,\ \sum_a c_{a,kl}c_{a,pq}=\delta_{kp}\delta_{lq}\bigr).$$
--
--   Neither coefficient in the inner sum is conjugated. In dimension $n=m=2$, the explicit family $F_{ij}=\mathrm i E_{ij}$ is linearly independent and spans $M_2(\mathbb C)$, and $J_{2,F}(\operatorname{id})\ne J_2(\operatorname{id})$.
--
--   The criterion and the concrete example establish basis dependence. The separate printed characterization in terms of $U^tU=I$ is deferred as false.
-- source:
--   The Jamio{\l}kowski isomorphism and a conceptionally simple proof for the correspondence between vectors having Schmidt number $k$ and $k$-positive maps, arXiv:quant-ph/0702255v1, PDF p. 6, §IV, basis-dependence paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P50

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P50

/-- PDF p.6, §IV basis-dependence paragraph: full coefficient expansion and
necessary-and-sufficient coefficient criterion, without conjugating either coefficient.
The final conjunct supplies an explicit n=m=2 basis-change witness. The distinct,
false printed U^t U = I characterization is deferred in HARD.md. -/
theorem j2_basis_coefficient_criterion {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (F : Module.Basis (Fin n × Fin n) ℂ ((Matrix (Fin n) (Fin n) ℂ))) :
    ((∀ T : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ),
        j2Family F T =
          ∑ b : Fin n × Fin n, ∑ c : Fin n × Fin n,
            (∑ a : Fin n × Fin n, F a b.1 b.2 * F a c.1 c.2) •
              Matrix.kronecker (Matrix.single b.1 b.2 1) (T (Matrix.single c.1 c.2 1))) ∧
      ((∀ T : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ), j2Family F T = j2 T) ↔
        ∀ b c : Fin n × Fin n,
          (∑ a : Fin n × Fin n, F a b.1 b.2 * F a c.1 c.2) =
            if b = c then 1 else 0)) ∧
      (LinearIndependent ℂ phaseBasis ∧
        Submodule.span ℂ (Set.range phaseBasis) = ⊤ ∧
        j2Family phaseBasis (LinearMap.id : (Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)) ≠
          j2 (LinearMap.id : (Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P50

end
