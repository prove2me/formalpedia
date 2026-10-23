-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartV_entry_19_2_1
-- name    : RamanujanLostNotebook.PartV.entry_19_2_1
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T18:42:20.960284+00:00
-- url     : https://prove2.me/theorems/4025ac0d-180b-4f7f-aa59-b50181a5c189
-- title:
--   The 5-dissection of the rank generating function at a fifth root of unity
-- statement:
--   Let $\zeta$ be a primitive fifth root of unity, $0<|q|<1$, $f_5(q)=\sum_{n\ge0}\frac{q^{n^2}}{(\zeta q;q)_n(\zeta^{-1}q;q)_n}$, $G(q)=\frac1{(q;q^5)_\infty(q^4;q^5)_\infty}$, $H(q)=\frac1{(q^2;q^5)_\infty(q^3;q^5)_\infty}$, $A=(q^5;q^5)_\infty G^2/H$, $B=(q^5;q^5)_\infty G$, $C=(q^5;q^5)_\infty H$, $D=(q^5;q^5)_\infty H^2/G$, $\Phi(q)=-1+\sum_{n\ge0}\frac{q^{5n^2}}{(q;q^5)_{n+1}(q^4;q^5)_n}$, $\Psi(q)=-1+\sum_{n\ge0}\frac{q^{5n^2}}{(q^2;q^5)_{n+1}(q^3;q^5)_n}$. Then $f_5(q)=A(q^5)+(\zeta+\zeta^{-1}-2)\Phi(q^5)+qB(q^5)+(\zeta+\zeta^{-1})q^2C(q^5)-(\zeta+\zeta^{-1})q^3\{D(q^5)-(\zeta^2+\zeta^{-2}-2)\Psi(q^5)/q^5\}$. Differs from the printed source: (19.2.8) prints $\Psi(q)/q=\sum q^{5n^2-1}/\cdots$, without the $-1$ of (5.1.13); the identity holds numerically only with the $-1$ (numerical evidence, not a proof; correction ours). Confirmed by the independent audit (its own computation, numerical evidence, not a proof): at q = 0.23, 0.17+0.11i, -0.29+0.08i and each of the four primitive fifth roots the form with the Ψ of (5.1.13) agrees to about 3e-64 relative, the literal (19.2.8) reading differs by 0.97–1.03 relative. This entry restates Entry 2.1.2 of Part III (p. 11 of that volume), which is also published; for $0<|q|<1$ the two formal statements say the same, and the Part III item also covers $q=0$.
--
--   **Discrepancy from the printed source.** Book p. 391, (19.2.8): Ψ(q)/q := Σ_{n≥0} q^{5n^2-1}/((q^2;q^5)_{n+1}(q^3;q^5)_n), i.e. Ψ(q) = Σ q^{5n^2}/(...). Book p. 60, (5.1.13): Ψ(q) = -1 + Σ q^{5n^2}/(...). Stated here with (5.1.13) (shared mtcPsi). Evidence: (19.2.9) holds to 60 digits at five points for each of the four primitive roots with (5.1.13) and fails by a relative error of order 1 with the literal (19.2.8). Numerical evidence, not a proof. Who: correction ours. Also added: q ≠ 0 (division by q^5). Confirmed by the independent audit (its own computation, numerical evidence, not a proof): at q = 0.23, 0.17+0.11i, -0.29+0.08i and each of the four primitive fifth roots the form with the Ψ of (5.1.13) agrees to about 3e-64 relative, the literal (19.2.8) reading differs by 0.97–1.03 relative.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 19, Entry 19.2.1, p. 391, eq. (19.2.9).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mtcPhi
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mtcPsi
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPoch
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPochInf
import Definitions.Def_RamanujanLostNotebook_PartV_shared_rankGen
import Definitions.Def_RamanujanLostNotebook_PartV_shared_rrGProd
import Definitions.Def_RamanujanLostNotebook_PartV_shared_rrHProd

namespace RamanujanLostNotebook.PartV
theorem entry_19_2_1 (ζ q : ℂ) (hζ : IsPrimitiveRoot ζ 5) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    rankGen ζ q
      = qPochInf (q ^ 25) (q ^ 25) * rrGProd (q ^ 5) ^ 2 / rrHProd (q ^ 5)
        + (ζ + ζ⁻¹ - 2) * mtcPhi (q ^ 5)
        + q * (qPochInf (q ^ 25) (q ^ 25) * rrGProd (q ^ 5))
        + (ζ + ζ⁻¹) * q ^ 2 * (qPochInf (q ^ 25) (q ^ 25) * rrHProd (q ^ 5))
        - (ζ + ζ⁻¹) * q ^ 3
          * (qPochInf (q ^ 25) (q ^ 25) * rrHProd (q ^ 5) ^ 2 / rrGProd (q ^ 5)
              - (ζ ^ 2 + ζ⁻¹ ^ 2 - 2) * (mtcPsi (q ^ 5) / q ^ 5)) := by sorry
end RamanujanLostNotebook.PartV
