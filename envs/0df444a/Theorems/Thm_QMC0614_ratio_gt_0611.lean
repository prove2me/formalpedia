-- Prove2me | Theorems.Thm_QMC0614_ratio_gt_0611
-- name    : QMC0614.ratio_gt_0611
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T14:55:04.725093+00:00
-- url     : https://prove2.me/theorems/a14597df-45d8-4d25-89b0-eccf7b81b783
-- title:
--   Min-max endgame of the $0.611$ quantum max-cut ratio ($d=14/15$, level $k=13$)
-- statement:
--   **The min-max endgame of the $0.611$ quantum max-cut ratio (level $k=13$)** (ALMPS25, arXiv:2504.15276, Section 4.2).
--
--   For one edge of a quantum max-cut instance, let $s=\tfrac13\operatorname{Tr}[(X_iX_j+Y_iY_j+Z_iZ_j)\rho]\in[-1,\tfrac13]$
--   be the *Pauli correlation*; the level-2 SDP bound on the edge's contribution is $\tfrac12(1-3s)$. The two rounding
--   strategies of the paper have per-edge ratio (energy over SDP bound)
--
--   $$E_M(s)=\frac{1+3d\,\bigl[-\tfrac{1+3s}{2}\bigr]^{+}}{1-3s},\qquad
--   E_{PM}(\sigma,s)=\frac{1-F(s)\cos^{2}\theta+d\,\sigma\bigl(1-F(s)(1+\sigma)\bigr)\bigl[-\tfrac{1+3s}{2}\bigr]^{+}}{1-3s},$$
--
--   with $\sigma=\sin\theta$, $F$ the BFV product expectation, and $[x]^{+}=\max\{x,0\}$ the rescaled integral-matching
--   weight. Mixing them with weight $\mu$ gives the certified ratio
--   $\alpha\ge\max_{\mu,\theta}\min_{s}\bigl(\mu E_{PM}(\sigma,s)+(1-\mu)E_M(s)\bigr)$.
--
--   **Theorem.** With the level-$13$ matching weight $d=14/15$, $\mu=0.861$ and $\sigma=\sin\theta=0.28086$
--   ($\theta\approx0.2847$ radians — the paper's certified point for this regime),
--   $$\forall s\in[-1,\tfrac13):\qquad 0.611\ <\ \mu\,E_{PM}(\sigma,s)+(1-\mu)\,E_M(s).$$
--   Hence the max-min value, and with it the approximation ratio of the "better of MATCH and PMATCH" algorithm, is
--   strictly larger than $0.611$.
--
--   **Where the constant comes from.** The bound is a per-edge comparison of energy against the SDP value; the
--   delicate range is $s\in[-1,-\tfrac13]$, where the matching weight $[-\tfrac{1+3s}{2}]^{+}$ becomes active and the
--   negative Pauli correlation simultaneously improves the product rounding. The proof uses only
--   $F(s)=\frac{8}{3\pi}s\,G(s^2)$ with $G\ge1$ (giving $F(s)\le0.8488\,s$ for $s\le0$), $G\ge1+x/8$ (giving
--   $F(s)\le0.8488\,s(1+s^{2}/8)$ for $s\le0$) and $F(s)\le s$ for $s\in[0,\tfrac13]$, and then certifies the
--   resulting one-variable polynomial inequality exactly, in the Bernstein basis, on three pieces.
--
--   *Formalization note.* The statement is about the published definitions `QuantumMaxCutBFVProductRounding`
--   (`BFVBound.F`, `QMC0614.EM`, `QMC0614.EPM`, `QMC0614.mixture`); the rational point $\sigma=0.28086$ approximates
--   $\sin(0.2847)=0.280854\ldots$.
-- source:
--   Anshu, Lee, Mousavi, Parekh, Soleimanifar, arXiv:2504.15276 (ESA 2025), Section 4.2, Eq. (19) and the sentence after Eq. (21) (d=14/15, theta=0.2847, mu=0.861 gives alpha>0.611); matching-polytope weights from GSS25 arXiv:2504.11120 Lemma 3.4/3.10; product side F from Brandao-Fernandes-Vallentin arXiv:0910.5765.

import Mathlib
import Definitions.Def_QuantumMaxCutBFVProductRounding
open scoped BigOperators

namespace QMC0614

theorem ratio_gt_0611 (s : ℝ) (h1 : -1 ≤ s) (h2 : s < 1 / 3) :
    (0.611 : ℝ) < mixture (14 / 15) 0.861 0.28086 s := by sorry

end QMC0614
