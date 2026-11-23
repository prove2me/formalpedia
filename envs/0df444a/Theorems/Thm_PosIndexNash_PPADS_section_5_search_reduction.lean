-- Prove2me | Theorems.Thm_PosIndexNash_PPADS_section_5_search_reduction
-- name    : PosIndexNash.PPADS.section_5_search_reduction
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:56:52.194071+00:00
-- url     : https://prove2.me/theorems/2bb091d7-d89d-4ee7-9bef-c689d08001d5
-- title:
--   Section 5 — positive-index fixed points reduce to positive exact LCP solutions
-- statement:
--   The normal-form construction of §5 yields a polynomial-time search reduction
--   $$\textsc{Positive-Index Fixed Point}\le_p\textsc{Positive-Index LCP}.$$
--   The instance map normalizes every max gate as $x_i=\max\{0,\ell_i(x_{<i},\lambda)\}$ and appends the anchored output gates (32). Thus $\Phi(\lambda)=V^\top x(\lambda)$ and $M=A-UV^\top$ have polynomial encoding length. By Lemma 5.3, $x$ solves $\mathrm{LCP}(M,-b)$ exactly when $\lambda=V^\top x$ is a fixed point and $x=x(\lambda)$. By Lemma 5.5, on $I=\operatorname{supp}(x)$,
--   $$\operatorname{sign}\det M_{I,I}=\operatorname{sign}\det(I_d-D\Phi(\lambda))=\operatorname{ind}_{\Phi}(\lambda).$$
--   Consequently a positive LCP answer decodes, using exact rational arithmetic and $V^\top x$, to a positive-index fixed-point answer. Lemma 5.6 supplies the polynomial-time exact decoding and bit-length bounds.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879, pp. 35–39, §5.1 normal form and Lemma 5.1, Lemma 5.3 (pp. 37–38), Lemma 5.5 (pp. 38–39), Lemma 5.6 (p. 39)

import Mathlib
import Definitions.Def_CardinalMatching_SearchReduces
import Definitions.Def_PosIndexNash_PPADS_PositiveIndexFixedPoint
import Definitions.Def_PosIndexNash_PPADS_PositiveIndexLCP

theorem PosIndexNash.PPADS.section_5_search_reduction :
    CardinalMatching.SearchReduces PositiveIndexFixedPoint PositiveIndexLCP := by sorry
