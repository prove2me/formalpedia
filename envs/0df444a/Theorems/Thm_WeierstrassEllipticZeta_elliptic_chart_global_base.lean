-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_chart_global_base
-- name    : WeierstrassEllipticZeta.elliptic_chart_global_base
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-20T21:23:07.318709+00:00
-- url     : https://prove2.me/theorems/4c7f10e7-8957-4cf0-80c7-dbf3bc2c4d56
-- title:
--   Globalization of chart base ideals and finiteness of component candidates
-- statement:
--   Let $S_0,\ldots,S_4:\mathbb C\to\mathbb C$ be entire functions. Use the two chart coordinate maps
--
--   $$v_0(z)=(z,S_1(z)/S_0(z),S_2(z)/S_0(z),S_3(z)/S_0(z)),$$
--   $$v_1(z)=(z,S_0(z)/S_2(z),S_1(z)/S_2(z),S_4(z)/S_2(z)).$$
--
--   Put $d_0=S_0$, $d_1=S_2$, and $U_j=\{z:d_j(z)\ne0\}$. In the ring $A=\mathbb C[X_0,X_1,X_2,X_3]$, define
--
--   $$K_{j,z}=\{p\in A:p(v_j(w))=0\text{ for all }w\text{ near }z\},
--   \qquad K_j^{\mathrm{glob}}=\{p\in A:p(v_j(w))=0\text{ for every }w\in U_j\}.$$
--
--   For every chart $j$ and every $z\in U_j$,
--
--   $$K_{j,z}=K_j^{\mathrm{glob}}.$$
--
--   Consequently, for every polynomial $Q\in\mathbb C[Y_0,\ldots,Y_6]$ and its previously defined chart normalization $Q_j$,
--
--   $$K_{j,z}+(Q_j)=K_j^{\mathrm{glob}}+(Q_j).$$
--
--   In particular the canonical base ideal, and hence each of its derivative ideals, is independent of the chosen available point within each chart.
--
--   Furthermore, for any period data $L$ and natural number $T$, the labeled candidate set
--
--   $$\{(j,i,\mathfrak p): j\in\{0,1\},\ i\in\{0,1,2\},\
--   \mathfrak p\in\operatorname{Min}(P_{iT}(J_j^{\mathrm{glob}}))\cap
--   \operatorname{Min}(P_{(i+1)T}(J_j^{\mathrm{glob}}))\}$$
--
--   is finite, where $J_j^{\mathrm{glob}}=K_j^{\mathrm{glob}}+(Q_j)$ and $P_r$ uses the fixed Weierstrass chart derivation associated with $L$.
--
--   **Formalization Note.** This gives a common family of affine ideals for the component argument in the zero-estimate framework of [Philippon (1986), §5, pp. 380–382](https://www.numdam.org/item/10.24033/bsmf.2060.pdf) and [Senthil Kumar (2026), Appendix A, Theorem A.2](https://doi.org/10.1017/S001309152610145X). The proof needs only that the $S_j$ are entire. It does not identify the orbit's relation ideal with the full algebraic-group ideal, glue the two charts, select the global stabilizer locus, or give a quantitative degree bound on the finite family.
-- source:
--   Philippon (1986), Lemmes de zeros dans les groupes algebriques commutatifs, Bull. Soc. Math. France 114, 355-383, section 5, pp. 380-382: global derivative ideals and finite families of components in the zero-estimate proof. https://www.numdam.org/item/10.24033/bsmf.2060.pdf. Senthil Kumar K (2026), Appendix A, Theorem A.2. https://doi.org/10.1017/S001309152610145X. The complete affine consistency theorem proves that the analytic-orbit germ kernel at any available chart point equals the ideal of relations vanishing on the entire available chart orbit. Thus the canonical base is independent of the point within each chart, and the labeled component candidates form one finite family. The old and global chart budget data are equivalent under the entire-coordinate hypothesis. Identification with the full algebraic-group ideal, gluing the two charts, locus selection and the uniform total-degree estimate remain outside this result.

import Definitions.Def_WeierstrassEllipticZeta_GlobalChartBase

open TranscendenceTheory WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.elliptic_chart_global_base
    (S : Fin 5 → ℂ → ℂ) (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ) :
    (∀ (c : Fin 2) (z : ℂ), S (extensionChartDenominator c) z ≠ 0 →
      analyticOrbitKernel (extensionChartEvalHom S c) z = extensionGlobalChartKernel S c ∧
      ∀ Q : MvPolynomial (Fin 7) ℂ,
        extensionChartBaseIdeal S Q c z = extensionGlobalChartBaseIdeal S Q c) ∧
    ∀ (L : PeriodPair) (Q : MvPolynomial (Fin 7) ℂ) (T : ℕ),
      (globalChartCandidates L S Q T).Finite := by sorry
