-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartV_entry_11_1_1
-- name    : RamanujanLostNotebook.PartV.entry_11_1_1
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T19:18:00.40798+00:00
-- url     : https://prove2.me/theorems/442f4e10-20bf-40a3-8a1c-cbe55d956677
-- title:
--   Tenth order mock theta functions: φ10(q), ψ10(-q^4), χ10(q^8) and a theta quotient
-- statement:
--   Let $0<|q|<1$, $\phi_{10}(q)=\sum_{n\ge0}\dfrac{q^{n(n+1)/2}}{(q;q^2)_{n+1}}$, $\psi_{10}(q)=\sum_{n\ge1}\dfrac{q^{n(n+1)/2}}{(q;q^2)_n}$, $X_{10}(q)=\sum_{n\ge0}\dfrac{(-1)^nq^{n^2}}{(-q;q)_{2n}}$, $\chi_{10}(q)=\sum_{n\ge1}\dfrac{(-1)^{n-1}q^{n^2}}{(-q;q)_{2n-1}}$, $\varphi(q)=\sum_{n\in\mathbb Z}q^{n^2}$, $\psi(q)=\sum_{n\ge0}q^{n(n+1)/2}$ and $h(q)=\sum_{n\in\mathbb Z}(-1)^nq^{n(5n+3)/2}$. Then $\phi_{10}(q)-q^{-1}\psi_{10}(-q^4)+q^{-2}\chi_{10}(q^8)=\dfrac{\varphi(q)\,h(-q^2)}{\psi(-q^2)}$. Differs from the printed source: the book prints the denominator $\psi(-q)$; that version fails numerically, the one with $\psi(-q^2)$ holds to 50 digits and in 41 Taylor coefficients (numerical evidence, not a proof; correction ours; confirmed by an independent audit computation at four points: residuals 0.26–0.63 for the printed form, below $1.4\times10^{-70}$ for this one); $q\ne0$ is added by us.
--
--   **Discrepancy from the printed source.** The book prints (11.1.1), p. 229, with the denominator $\psi(-q)$, and the last display of its proof (p. 248) repeats $\psi(-q)$. We state it with $\psi(-q^2)$. Evidence: with $\psi(-q^2)$ the two sides agree to 50 digits at four values of q and in the Taylor coefficients of $q^0,\dots,q^{40}$; with $\psi(-q)$ they differ by 26%–49% at the same four points (already in the coefficient of $q$). The book says on p. 230 that it replaced $q$ by $q^2$ in Ramanujan's formulation; the printed denominator looks like a place where that substitution was not carried out. Numerical evidence, not a proof; the correction is ours (it is also recorded in part5/shared/QSERIES_NOTES.md, section 6). The hypothesis $q\ne0$ (for $q^{-1}$, $q^{-2}$) is added by us. Confirmed by the independent Codex audit (own code, 70 digits, $q=0.3$, $0.25+0.3i$, $-0.4+0.1i$, $0.61+0.1i$): printed form, relative residuals 0.25903884, 0.27907046, 0.44357683, 0.62575001; form with $\psi(-q^2)$, below 1.4e-70 at all four points.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 11, Entry 11.1.1, p. 229, eq. (11.1.1).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_ch11_ch11H
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mockChi10
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mockPhi10
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mockPsi10
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPoch
import Definitions.Def_RamanujanLostNotebook_PartV_shared_thetaPhi
import Definitions.Def_RamanujanLostNotebook_PartV_shared_thetaPsi

namespace RamanujanLostNotebook.PartV
theorem entry_11_1_1 (q : ℂ) (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    mockPhi10 q - q⁻¹ * mockPsi10 (-(q ^ 4)) + (q ^ 2)⁻¹ * mockChi10 (q ^ 8) =
      thetaPhi q * ch11H (-(q ^ 2)) / thetaPsi (-(q ^ 2)) := by sorry
end RamanujanLostNotebook.PartV
