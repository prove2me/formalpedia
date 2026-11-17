-- Prove2me | Theorems.Thm_PersistQMem_Supplement_theorem_9_1
-- name    : PersistQMem.Supplement.theorem_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:18:41.621267+00:00
-- url     : https://prove2.me/theorems/068a2958-d642-419e-850d-373c309e1ed8
-- title:
--   Theorem 9.1 — finite shared-memory composition
-- statement:
--   Let $\Phi_1,\Phi_2$ be completely positive maps on one joint-source matrix space. Let $\mathcal A_1,\mathcal A_2$ be completely positive, Hilbert–Schmidt self-adjoint, and commuting. If
--
--   $$
--   \Phi_i\preceq_{\mathrm{CP}}a_i\mathcal A_i^{2d_i},\qquad a_i\ge0,\quad d_i\ge1,
--   $$
--
--   set $d=d_1+d_2$, $\mathcal A=\mathcal A_1+\mathcal A_2$, and
--
--   $$
--   c=\frac{a_1a_2}{\binom{2d}{2d_1}}.
--   $$
--
--   Then $\Phi_1\Phi_2\preceq_{\mathrm{CP}}c\mathcal A^{2d}$. If $p\ge d$ and $H_p$ bounds $\operatorname{Tr}(\rho\mathcal A^{2p}(\rho))$ for every pure state on this same joint source, every $T\succeq0$ with $\operatorname{Tr}(T^2)=1$ and $\operatorname{rank}T\le K$ satisfies
--
--   $$
--   \operatorname{Tr}(T\Phi_1\Phi_2(T))\le c(KH_p)^{d/p}.
--   $$
--
--   If $\Phi_1\Phi_2=\sum_{j=1}^M\operatorname{Ad}_{C_j}$ for distinct orthogonal centered Hermitian reflections, every successful simultaneous signed estimator with error $0<\epsilon\le1/8$, success $2/3$, and one shared retained dimension at most $K$ obeys
--
--   $$
--   N\ge\frac{M}{20\epsilon^2(c(KH_p)^{d/p}+2K-2)}.
--   $$
--
--   Differences from the source:
--   - encoding: finite-dimensional CP maps and Hilbert–Schmidt operations in mathematical notation → complex-linear maps on $D\times D$ matrices with the published amplification definition of complete positivity; reason: this is the same finite-dimensional matrix-space object
--   - encoding: implicit positive source and memory dimensions → hypotheses $D\ge1$ and $K\ge1$; reason: they only exclude undefined zero-dimensional physical systems
--   - encoding: every simultaneous signed-estimation receiver → every achievable cap under the published protocol with a measurable real-vector terminal POVM density; reason: this unfolds the same task, source independence, shared memory charge, and copy cap in the source model's density representation
--   - encoding: distinct orthogonal centered Hermitian reflections → injectivity, Hermiticity, $C_j^2=I$, zero trace, and $\operatorname{Tr}(C_iC_j)=D\mathbf1_{i=j}$; reason: these are exactly the finite-dimensional normalized clauses used by the source
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), Theorem 9.1, (96)–(100), pp.39–40 (PDF pp.42–43)

import Mathlib
import Definitions.Def_PersistQMem_Supplement_Achievable
import Definitions.Def_PersistQMem_Supplement_CPLe

set_option autoImplicit false

open scoped Matrix ComplexOrder

namespace PersistQMem
namespace Supplement

/-- **Theorem 9.1 (Finite shared-memory composition), pp.39--40** (Tao--Shen,
*Structural Lower Bounds for Quantum Property Estimation with Persistent Memory*, STOC 2027
submission, manuscript of 2026-11-03, sha256 6d48ad24..., Theorem 9.1, (96)--(100),
pp.39--40, PDF pp.42--43).

The statement includes the CP-order composition rule (98), the rank-`K` moment estimate (99), and the
simultaneous-estimation consequence (100).  All maps act on the same `D x D` joint-source matrix space;
the moment hypothesis ranges over every rank-one density matrix on that space, and the single rank and
memory charge is `c (K H)^(d/p) + 2K - 2`.

**Formalization Note.** Products of maps are composition (`Phi1.comp Phi2`).  Hilbert--Schmidt
self-adjointness is `IsHSSelfAdjoint`, CP order is `CPLe`, and the source's finite-dimensional CP notion
is the published `QAlgorithms.Entanglement.IsCompletelyPositive`.  Positive source dimension and
`K >= 1` only make explicit that `C^D` and a retained memory are genuine nonempty spaces. -/
theorem theorem_9_1 (D M K : Nat) (hD : 1 <= D) (hK : 1 <= K)
    (Phi1 Phi2 A1 A2 : SourceMap D)
    (hPhi1 : QAlgorithms.Entanglement.IsCompletelyPositive Phi1)
    (hPhi2 : QAlgorithms.Entanglement.IsCompletelyPositive Phi2)
    (hA1 : QAlgorithms.Entanglement.IsCompletelyPositive A1)
    (hA2 : QAlgorithms.Entanglement.IsCompletelyPositive A2)
    (hA1self : IsHSSelfAdjoint A1) (hA2self : IsHSSelfAdjoint A2)
    (hcomm : Commute A1 A2)
    (a1 a2 : Real) (ha1 : 0 <= a1) (ha2 : 0 <= a2)
    (d1 d2 : Nat) (hd1 : 1 <= d1) (hd2 : 1 <= d2)
    (h96_1 : CPLe Phi1 ((a1 : Complex) • (A1 ^ (2 * d1))))
    (h96_2 : CPLe Phi2 ((a2 : Complex) • (A2 ^ (2 * d2))))
    (p : Nat) (hp : d1 + d2 <= p) (H : Real)
    (hH : BoundsPureMoment (A1 + A2) p H) :
    let d := d1 + d2
    let A := A1 + A2
    let c := a1 * a2 / (Nat.choose (2 * d) (2 * d1) : Real)
    CPLe (Phi1.comp Phi2) ((c : Complex) • (A ^ (2 * d))) /\
    (forall T : SourceMatrix D, T.PosSemidef -> (T * T).trace = 1 -> T.rank <= K ->
      (T * ((Phi1.comp Phi2) T)).trace.re <=
        c * Real.rpow ((K : Real) * H) ((d : Real) / (p : Real))) /\
    (forall C : Fin M -> SourceMatrix D,
      IsOrthogonalReflectionFamily C -> Phi1.comp Phi2 = reflectionMap C ->
      forall epsilon : Real, 0 < epsilon -> epsilon <= 1 / 8 ->
      forall N : Nat, Achievable C K epsilon N ->
        (M : Real) /
            (20 * epsilon ^ 2 *
              (c * Real.rpow ((K : Real) * H) ((d : Real) / (p : Real)) +
                2 * (K : Real) - 2)) <=
          (N : Real)) := by sorry

end Supplement
end PersistQMem
