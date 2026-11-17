-- Prove2me | Theorems.Thm_PersistQMem_Supplement_theorem_2_7
-- name    : PersistQMem.Supplement.theorem_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:17:08.11638+00:00
-- url     : https://prove2.me/theorems/08985e40-5556-4c0f-b0dc-4e597741711a
-- title:
--   Theorem 2.7 — quadratic cross correlations
-- statement:
--   Let $n\ge1$, $K\ge1$, and $0<\epsilon\le1/8$. For the $M=[n(2n-1)]^2$ quadratic Majorana cross observables on the joint two-factor source, put $\mathcal A(X)=\sum_{r=1}^{4n}c_rXc_r$. For every integer $p\ge2$, any finite $H_p(4n)$ satisfying
--
--   $$
--   H_p(4n)\ge\sup_{\rho\ \mathrm{pure}}\operatorname{Tr}(\rho\mathcal A^{2p}(\rho))
--   $$
--
--   gives, for every achievable cap $N$,
--
--   $$
--   N\ge\frac{M}{20\epsilon^2\left((K H_p(4n))^{2/p}/24+2K-2\right)}.
--   $$
--
--   For every even $L\ge2$ and $p\ge1$,
--
--   $$
--   \widehat H_p(L)=\frac{(2p)!}{p!}\left(\frac{(1+e)L}{2}\right)^p
--   \le((1+e)pL)^p
--   $$
--
--   is such a pure-state moment certificate. If $n\ge2$ and $K_0=\lfloor\sqrt n\rfloor$, then
--
--   $$
--   \frac{n^2}{2500\epsilon^2(1+\ln n)^2}\le N^*(n,K_0,\epsilon)
--   \le(2n-1)^2\left\lceil2\epsilon^{-2}\ln(6M)\right\rceil
--   \le36n^2\epsilon^{-2}\ln(4n).
--   $$
--
--   The displayed upper cap is achievable with retained dimension one, and the ratio of the displayed upper and lower bounds is at most $90000(1+\ln n)^2\ln(4n)$.
--
--   Differences from the source:
--   - encoding: the least worst-case budget $N^*$ → lower bounds for every achievable cap plus explicit achievable upper caps; reason: equivalent for this finite family and records the dimension-one witness directly
--   - encoding: an arbitrary final measurement producing a real output vector → a jointly measurable POVM density on the same real-vector output space against an s-finite reference kernel; reason: this is the measurable density representation used by the published protocol model and changes no receiver instance
--   - encoding: abstract canonical local and global Majoranas → their standard Jordan–Wigner matrices on the joint $2n$-qubit source; reason: this is the representation specified for implementation and is unitarily equivalent to the canonical finite Clifford representation
--   - encoding: every even integer $L\ge2$ → $L=2m$ with $m\ge1$; reason: these parameterizations are equivalent
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), Theorem 2.7, (14)–(18), p.7 (PDF p.10)

import Mathlib
import Definitions.Def_PersistQMem_Supplement_Achievable
import Definitions.Def_PersistQMem_Supplement_IsMajoranaCrossFamily
import Definitions.Def_PersistQMem_Supplement_CPLe

set_option autoImplicit false

namespace PersistQMem
namespace Supplement

/-- **Theorem 2.7 (Quadratic cross correlations), p.7** (Tao--Shen, *Structural Lower
Bounds for Quantum Property Estimation with Persistent Memory*, STOC 2027 submission,
manuscript of 2026-11-03, sha256 6d48ad24..., Theorem 2.7, (14)--(18), p.7,
PDF p.10).

This single statement retains the arbitrary finite moment-certificate implication (16), the all-even-size
certificate and both inequalities in (17), and the three finite bounds and ratio claim in (18).  The
unknown source ranges over all joint density matrices through `Achievable`, so entangled and
parity-coherent sources are included, and `K` is one shared retained product dimension.

**Formalization Note.** The canonical global Majoranas use the Jordan--Wigner representation on the
joint `2n`-qubit source; `IsMajoranaCrossFamily` records an enumeration of the `M` cross observables.
As in Theorem 2.5, `N*` is rendered operationally by lower-bounding every achievable cap and providing
the displayed achievable cap, including its dimension-one witness. -/
theorem theorem_2_7 (n K : Nat) (hn : 1 <= n) (hK : 1 <= K)
    (epsilon : Real) (he0 : 0 < epsilon) (he1 : epsilon <= 1 / 8)
    (G : Fin (crossCount n) ->
      Matrix (Fin (2 ^ (2 * n))) (Fin (2 ^ (2 * n))) Complex)
    (hG : IsMajoranaCrossFamily n G) :
    let M := crossCount n
    let A := majoranaMap n
    (forall p : Nat, 2 <= p -> forall H : Real, BoundsPureMoment A p H ->
      forall N : Nat, Achievable G K epsilon N ->
        (M : Real) /
          (20 * epsilon ^ 2 *
            (Real.rpow ((K : Real) * H) (2 / (p : Real)) / 24 + 2 * (K : Real) - 2)) <=
          (N : Real)) /\
    (forall m p : Nat, 1 <= m -> 1 <= p ->
      BoundsPureMoment (cliffordMap m) p (majoranaCertificate p (2 * m)) /\
      majoranaCertificate p (2 * m) <=
        (((1 + Real.exp 1) * (p : Real) * (2 * m : Nat)) : Real) ^ p) /\
    (2 <= n ->
      let K0 := ⌊Real.sqrt (n : Real)⌋₊
      let U := (2 * n - 1) ^ 2 *
        ⌈2 * epsilon⁻¹ ^ 2 * Real.log (6 * (M : Real))⌉₊
      (forall N : Nat, Achievable G K0 epsilon N ->
        (n : Real) ^ 2 /
          (2500 * epsilon ^ 2 * (1 + Real.log (n : Real)) ^ 2) <= (N : Real)) /\
      Achievable G K0 epsilon U /\
      Achievable G 1 epsilon U /\
      (U : Real) <= 36 * (n : Real) ^ 2 * epsilon⁻¹ ^ 2 * Real.log (4 * (n : Real)) /\
      (U : Real) /
          ((n : Real) ^ 2 /
            (2500 * epsilon ^ 2 * (1 + Real.log (n : Real)) ^ 2)) <=
        90000 * (1 + Real.log (n : Real)) ^ 2 * Real.log (4 * (n : Real))) := by sorry

end Supplement
end PersistQMem
