-- Prove2me | Theorems.Thm_QMC0614_ratio_gt_0614
-- name    : QMC0614.ratio_gt_0614
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T14:50:09.663325+00:00
-- url     : https://prove2.me/theorems/299c6981-79ce-4978-b65d-a1a5e56cb7b7
-- title:
--   Min-max endgame of the $0.614$ quantum max-cut ratio: $\mu E_{PM}+(1-\mu)E_M>0.614$ on $[-1,1/3)$
-- statement:
--   **The three-parameter min-max endgame of the $0.614$ quantum max-cut analysis** (ALMPS25, arXiv:2504.15276, Section 4.2).
--
--   Consider one edge of a quantum max-cut instance, in the level-2 (Pauli-moment) relaxation. Let
--   $$s=\tfrac13\operatorname{Tr}\big[(X_iX_j+Y_iY_j+Z_iZ_j)\rho\big]\in[-1,\tfrac13]$$
--   be the edge's *Pauli correlation*; the SDP certifies that the edge contributes at most $\tfrac12(1-3s)$ to the
--   objective. Two rounding algorithms are available:
--
--   * **MATCH** — go to a matching-state solution. With matching-polytope weight $d$ its energy, divided by the SDP
--     bound, is $E_M(s)=\dfrac{1+3d\,[-\frac{1+3s}{2}]^{+}}{1-3s}$.
--   * **PMATCH** — partially dephase by an angle $\theta$ and then round to a product state, at $t_{ij}$ with
--     expectation $F(s)$, the BFV product expectation. Writing $\sigma=\sin\theta$, its ratio is
--     $$E_{PM}(\sigma,s)=\frac{1-F(s)\cos^2\theta+d\,\sigma\bigl(1-F(s)(1+\sigma)\bigr)\bigl[-\frac{1+3s}{2}\bigr]^{+}}{1-3s}.$$
--
--   Mixing the two with weight $\mu$, the analysis reduces the approximation ratio to
--   $$\alpha\ \ge\ \max_{\mu\in[0,1],\ \theta\in[0,\pi/2]}\ \min_{s\in[-1,1/3)}\ \bigl(\mu E_{PM}(\sigma,s)+(1-\mu)E_M(s)\bigr).$$
--
--   **Theorem.** At the certified point $\mu=0.881$, $\sigma=\sin\theta=0.28068$ (that is $\theta\approx0.2845$
--   radians, the point used in the paper) and $d=1$ — the weight available for the augmented second-level SDP with a
--   separation oracle — the inner minimum exceeds $0.614$:
--   $$\forall s\in[-1,\tfrac13):\qquad 0.614\ <\ \mu\,E_{PM}(\sigma,s)+(1-\mu)\,E_M(s).$$
--   Consequently the max-min value, hence the approximation ratio of the "better of MATCH and PMATCH" algorithm, is
--   strictly larger than $0.614$.
--
--   **Why the bracket matters.** The weight $[-(1+3s)/2]^+$ vanishes for $s\ge-1/3$ and grows to $1$ at $s=-1$; it is
--   the rescaled weight of the integral matching polytope (GSS25 Lemma 3.4/3.10). On $s\in[-1/3,1/3)$ only the product
--   term is active and the bound is easy; the delicate range is $s\in[-1,-1/3]$, where both a negative Pauli
--   correlation *helps* the product rounding (the numerator gains $|F(s)|\cos^2\theta$) and the matching term grows.
--
--   **Proof.** (i) For $s\in[0,1/3]$ one uses the crude upper bound $F(s)\le s$; (ii) for $s\in[-1/3,0]$ the bound
--   $F(s)\le0.8488\,s$ (from $G\ge1$ in $F=\frac{8}{3\pi}sG(s^2)$); both give a *linear* inequality in $s$ with slack.
--   (iii) On $s\in[-1,-1/3]$ one uses the sharper $F(s)\le0.8488\,s\,(1+s^2/8)$ (from $G\ge1+x/8$), and the resulting
--   quartic polynomial in $s$ is certified nonnegative on the three pieces $[-1,-\tfrac12]$,
--   $[-\tfrac12,-\tfrac{5}{12}]$, $[-\tfrac{5}{12},-\tfrac13]$ by writing it in the Bernstein basis with strictly
--   positive rational coefficients. All constants are rational, so the certification is exact.
--
--   *Formalization note.* The statement is about the published definitions `QuantumMaxCutBFVProductRounding`
--   (`BFVBound.F`, `QMC0614.EM`, `QMC0614.EPM`, `QMC0614.mixture`); `σ = 0.28068` is a rational approximation of
--   $\sin(0.2845)=0.280678\ldots$, and the proof certifies the inequality at that rational point. The quotient is
--   cleared with $1-3s>0$, and the surviving polynomial inequality is decided by explicit Bernstein certificates.
-- source:
--   Anshu, Lee, Mousavi, Parekh, Soleimanifar, arXiv:2504.15276 (ESA 2025), Section 4.2, Eqs. (19), (20), (21) and the certified point stated after Eq. (21) (d=1, theta=0.2845, mu=0.881 gives alpha>0.614); matching-polytope weights from GSS25 arXiv:2504.11120 Lemma 3.4/3.10; product side F from Brandao-Fernandes-Vallentin arXiv:0910.5765 and PT22 Eq. (3).

import Mathlib
import Definitions.Def_QuantumMaxCutBFVProductRounding
open scoped BigOperators

namespace QMC0614

theorem ratio_gt_0614 (s : ℝ) (h1 : -1 ≤ s) (h2 : s < 1 / 3) :
    (0.614 : ℝ) < mixture 1 0.881 0.28068 s := by sorry

end QMC0614
