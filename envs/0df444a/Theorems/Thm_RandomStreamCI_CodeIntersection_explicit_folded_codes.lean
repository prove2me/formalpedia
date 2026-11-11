-- Prove2me | Theorems.Thm_RandomStreamCI_CodeIntersection_explicit_folded_codes
-- name    : RandomStreamCI.CodeIntersection.explicit_folded_codes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:30:25.66791+00:00
-- url     : https://prove2.me/theorems/2b9e448c-7f24-44a7-ace1-74ee57676579
-- title:
--   Proposition 7 — Explicit folded codes and simultaneous dual decoding
-- statement:
--   For every $0<c<c'<1$ there exists an explicit folded Reed–Solomon family $C_n\subseteq(\mathbb F_q^m)^n$, for every sufficiently large integer blocklength, with
--
--   $$q=\Theta(n^2),\quad m=\Theta(n),\quad \log_2|\Sigma|=\Theta(n\log_2 n),\quad \log_2|C_n|=O(n^2\log_2 n).$$
--
--   There are a fixed $0<\rho<1$ and total-list bounds $\ell=2^{\Theta(n^c)}$, $L=2^{\widetilde O(n^{c'})}\le2^{o(n)}$ for which the same codes are $(\rho,\ell,L)$-list recoverable. There is one deterministic polynomial-time decoder for their base-field linear duals such that
--
--   $$\Pr_{e\sim D^n}[\forall x\in C_n^\perp,\ \operatorname{Decode}(x+e)=x]\ge1-2^{-an}$$
--
--   for some $a>0$, eventually. Here $D$ has mass $1/2$ at zero and mass $1/(2(|\Sigma|-1))$ at each nonzero symbol. Explicitness, all growth constants, a polylogarithmic exponent in the list bound, and the decoder are uniform in $n$. This supplies the common code family for both space bounds.
--
--   Differences from the source:
--   - encoding: coordinates and times numbered from one → Fin indices numbered from zero; reason: the order-preserving relabelling preserves every source instance
--   - encoding: explicit folded family and polynomial-time deterministic dual decoder with asymptotic bounds → published folded-evaluation image over publicly named finite fields, uniform finite Turing machines and eventual quantified growth bounds; reason: finite-field labels and polynomially equivalent unary encodings fix representations; all constants and thresholds are uniform in blocklength
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Proposition 7, printed p. 8 / PDF p. 8 (statement spans pp. 8–9)

import Definitions.Def_RandomStreamCI_CodeIntersection_Codes

noncomputable section

namespace RandomStreamCI.CodeIntersection

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Proposition 7, pp. 8–9: every scaling, total-list recovery, explicitness, and simultaneous dual decoding, for the same family. -/
theorem explicit_folded_codes (c c' : ℝ) (hc : 0 < c) (hcc : c < c') (hc' : c' < 1) :
    ∃ F : CodeFamily, FamilyProperties F c c'  := by sorry

end RandomStreamCI.CodeIntersection
