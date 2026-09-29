-- Prove2me | Theorems.Thm_TateCurve_ks17_A_exports
-- name    : TateCurve.ks17_A_exports
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/cb303a7d-9e75-55de-ba6f-44578599cf7d
-- title:
--   Expansion-layer interface for the Tate curve addition law
-- statement:
--   Throughout, $K$ is a complete nontrivially normed field whose distance is ultrametric, and for such $K$ one writes $X(w)=$ `pointX q w`, $Y(w)=$ `pointY q w`, $\psi_N(u)=$ `psiCoeffFull u N` $=2\,$`yCoeffFull`$(u,N)+$`xCoeffFull`$(u,N)$, `curve q` $=\langle 1,0,0,a_4(q),a_6(q)\rangle$, `symSumNum` $q\,x_1x_2=2x_1x_2(x_1+x_2)+x_1x_2+2a_4(q)(x_1+x_2)+4a_6(q)$, `addDefectSum` $q\,u\,v=(X(uv)+X(uv^{-1}))(X(u)-X(v))^2-$`symSumNum`$q\,X(u)\,X(v)$ and `addDefectDiff` $q\,u\,v=(X(uv)-X(uv^{-1}))(X(u)-X(v))^2+$`pointPsiTwo`$q\,u\cdot$`pointPsiTwo`$q\,v$; `addDefectSumCoeff` and `addDefectDiffCoeff` are the stated explicit integral combinations of Cauchy products of `xCoeffFull`, `psiCoeffFull`, `a₄Coeff`, `a₆Coeff`, and `ExpansionRegion q u v` asserts `AddParams q u v` together with $\|q\|<1$ and $\|q\|<\|w\|$, $\|q\|\,\|w\|<1$ for $w\in\{u,v,uv,uv^{-1}\}$. The assertion is the conjunction of seventeen statements: $\psi_0(u)=2u^2/(1-u)^3+u/(1-u)^2$; $\psi_{N+1}(u)=\sum_{d\mid N+1}d^2(u^d-u^{-d})$; coefficient uniqueness, namely $A=B_c$ pointwise whenever for some $\varepsilon>0$ the two power series $\sum A_Nq'^N$, $\sum B_{c,N}q'^N$ have a common sum for every $q'\neq 0$ with $\|q'\|<\varepsilon$; invariance `addDefectDiff` $q\,(qu)\,v=$ `addDefectDiff` $q\,u\,v$ for $q\neq 0$; membership in `ExpansionRegion q' w v` from $q'\neq0$, $\|q'\|<\|w\|$, $\|q'\|\,\|w\|<1$, $\|w\|\neq1$, $\|v\|=1$, $v\neq1$; two transfer principles turning a coefficient identity valid on the expansion region — a row expansion $\sum_{k=1}^{M}\bigl(\sum_{j\in s_{M,k}}a_{M,k,j}v'^j\bigr)(u'^k+u'^{-k}-2)$ for `addDefectSumCoeff`, respectively $f\,u'\,v'\,M=$ `addDefectDiffCoeff` $u'\,v'\,M$ — into the summability statements that these coefficients against $q'^M$ sum to `addDefectSum` $q'\,u'\,v'$, respectively `addDefectDiff` $q'\,u'\,v'$; vanishing of `addDefectDiffCoeff` $u\,v\,0$ and of `addDefectSumCoeff` $u\,v\,0$ when $u,v\neq0$, $u,v\neq1$, $uv\neq1$, $uv^{-1}\neq1$; $y-$ `negY` $x\,y=2y+x$ on `curve q`; two extension lemmas deducing, for $q\neq0$, $\|q\|<1$, `AddParams q u v` and $\neg($`OnHalfLattice` $q\,u\wedge$ `OnHalfLattice` $q\,v)$, the symmetric sum identity $(X(uv)+X(uv^{-1}))(X(u)-X(v))^2=$ `symSumNum`$q\,X(u)\,X(v)$, respectively the difference identity with right-hand side $-(2Y(u)+X(u))(2Y(v)+X(v))$, from its validity on the whole expansion region; $\neg$`OnHalfLattice` $q\,w$ (no $m\in\mathbb Z$ with $\|q^mw\|^2=\|q\|$) when $q\neq0$, $\|q\|<1$, $\|w\|=1$; the $q$-expansion $\sum_N$ `addDefectSumCoeff` $u\,v\,N\cdot q^N=$ `addDefectSum` $q\,u\,v$ on the expansion region; two equivalences stating that `addDefectDiff` $q\,u\,v=0$ iff the difference identity holds, with the right-hand side written via $2Y+X$ or via $Y-$`negY`$(X,Y)$; and stability of `AddParams q u v` under replacing $u,v$ by any $u',v'$ with $u'=q^mu^{\pm1}$, $v'=q^{m'}v^{\pm1}$.
--
--   These are the interface lemmas of the $q$-expansion layer in the analytic verification that the Tate parametrisation of $E_q:y^2+xy=x^3+a_4(q)x+a_6(q)$ satisfies the symmetric addition identities for the $x$- and $y$-coordinates: coefficient extraction and uniqueness, the shape of the $\psi$-coefficients, passage from region-valid identities to identities for all admissible parameters off the half-lattice, and the resulting vanishing criteria for the sum and difference defects. They are consumed by the unconditional form of the difference identity [`TateCurve.diffHyp_unconditional`](thm.html#TateCurve.diffHyp_unconditional) and by the further export bundles [`TateCurve.ks17_B_exports`](thm.html#TateCurve.ks17_B_exports), [`TateCurve.ks17_C1_exports`](thm.html#TateCurve.ks17_C1_exports).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_ks17_A_exports.lean

import Mathlib
import Definitions.Def_TateCurve_XMultIdentities
import Definitions.Def_TateCurve_KeystoneVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal
open TateCurve FLT.DivisorConvolution FLT.DivisorConvolution.BesgeCertificate Finset

theorem TateCurve.ks17_A_exports.{u_1} :

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K},
      psiCoeffFull u 0 = 2 * yfun u + xfun u) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} (N : ℕ),
      psiCoeffFull u (N + 1) = ∑ d ∈ (N + 1).divisors, (d : K) ^ 2 * (u ^ d - u⁻¹ ^ d)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {A Bc : ℕ → K} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ q' : K, q' ≠ 0 → ‖q'‖ < ε → ∃ S : K,
      HasSum (fun N => A N * q' ^ N) S ∧ HasSum (fun N => Bc N * q' ^ N) S),
      ∀ N, A N = Bc N) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K} (hq0 : q ≠ 0),
      addDefectDiff q (q * u) v = addDefectDiff q u v) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q' w v : K} (hq'0 : q' ≠ 0)
    (hlo : ‖q'‖ < ‖w‖) (hhi : ‖q'‖ * ‖w‖ < 1) (hwne : ‖w‖ ≠ 1)
    (hv : ‖v‖ = 1) (hv1 : v ≠ 1),
      ExpansionRegion q' w v) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (hrow : ∀ q' u' v' : K, ExpansionRegion q' u' v' → ∀ M : ℕ,
      addDefectSumCoeff u' v' M
        = ∑ k ∈ Finset.Icc 1 M, (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k + u'⁻¹ ^ k - 2)),
      ∀ q' u' v' : K, ExpansionRegion q' u' v' → HasSum (fun M : ℕ => (∑ k ∈ Finset.Icc 1 M, (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k + u'⁻¹ ^ k - 2)) * q' ^ M) (addDefectSum q' u' v')) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {f : K → K → ℕ → K}
    (hcoeff : ∀ q' u' v' : K, ExpansionRegion q' u' v' → ∀ M : ℕ,
      f u' v' M = addDefectDiffCoeff u' v' M),
      ∀ q' u' v' : K, ExpansionRegion q' u' v' → HasSum (fun M : ℕ => f u' v' M * q' ^ M) (addDefectDiff q' u' v')) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huv : u * v ≠ 1) (huv' : u * v⁻¹ ≠ 1),
      addDefectDiffCoeff u v 0 = 0) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (q x y : K),
      y - (curve q).toAffine.negY x y = 2 * y + x) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hreg : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (hp : AddParams q u v) (hloc : ¬ (OnHalfLattice q u ∧ OnHalfLattice q v)),
      (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 = symSumNum q (pointX q u) (pointX q v)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hreg : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v')))
    (hp : AddParams q u v) (hloc : ¬ (OnHalfLattice q u ∧ OnHalfLattice q v)),
      (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 = -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q w : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hw : ‖w‖ = 1),
      ¬ OnHalfLattice q w) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K} (hreg : ExpansionRegion q u v),
      HasSum (fun N : ℕ => addDefectSumCoeff u v N * q ^ N) (addDefectSum q u v)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huv : u * v ≠ 1) (huv' : u * v⁻¹ ≠ 1),
      addDefectSumCoeff u v 0 = 0) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K},
      addDefectDiff q u v = 0 ↔ (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 = -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K},
      addDefectDiff q u v = 0 ↔ (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 = -((pointY q u - (curve q).toAffine.negY (pointX q u) (pointY q u)) * (pointY q v - (curve q).toAffine.negY (pointX q v) (pointY q v)))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K} {u' v' : K} (hp : AddParams q u v)
    (hu' : LatticeRep q u u') (hv' : LatticeRep q v v'),
      AddParams q u' v') := by sorry
