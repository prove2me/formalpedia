-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P32_conditional_broadcast_capacity
-- name    : QAlgorithms.Papers.Independent.Next46.P32.conditional_broadcast_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:29:09.222213+00:00
-- url     : https://prove2.me/theorems/496bde42-1c0b-4aa8-86bb-707b3b6ca5f5
-- title:
--   Conditional coherent-state capacity region
-- statement:
--   The channel acts on the full countable Fock space with independent fixed vacuum environment modes. Messages are independent and uniform on finite nonempty sets, arbitrary block density operators are allowed, and the receivers use separate POVMs. Let $\mathcal C$ denote the convex hull of the closure of achievable nonnegative rate pairs, measured in nats per use, using vanishing maximal joint error: Bob decodes both messages and Charlie decodes his own. The energy constraint is unconditional, averaged over messages and uses, with total block expectation at most $n\bar N$. Write $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$.
--
--   Let $1/2<\eta\le1$ and $\bar N\ge0$. Assume globally Strong Conjecture 2: mixing an arbitrary $n$-mode input of entropy $ng(K)$ with vacuum, retaining intensity $1-\theta$ of that input, has output entropy at least $ng((1-\theta)K)$, attained by identical thermal modes, for all $n\ge1$, $0\le\theta\le1$ and $K\ge0$. Then
--
--   $$
--   \mathcal C=\mathcal C_{\mathrm{coh}}=
--   \bigcup_{0\le\beta\le1}\{(R_B,R_C)\ge0:
--   R_B\le g(\eta\beta\bar N),\quad
--   R_C\le g((1-\eta)\bar N)-g((1-\eta)\beta\bar N)\}.
--   $$
--
--   Here $\mathcal C_{\mathrm{coh}}$ restricts input codewords to products of coherent states but still permits collective block measurements within each receiver. Thus this capacity formula is conditional on the unrestricted entropy conjecture.
-- source:
--   Classical capacity of bosonic broadcast communication and a new minimum output entropy conjecture, arXiv:0706.3416v1, PDF p. 1, Section IV, Eqs. (1), (16)-(17); PDF pp.1,3-5

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P32

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity productCoeff)

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Section IV, PDF pp.1,3-5, (1),(16)-(17): conditional ultimate capacity.
The hypothesis is the globally quantified conjecture about the vacuum degrading
map, not an entropy inequality postulated for the original splitter outputs. -/
theorem conditional_broadcast_capacity (eta Nbar : ℝ)
    (heta : 1 / 2 < eta) (heta1 : eta ≤ 1) (hNbar : 0 ≤ Nbar)
    (hconj : StrongConjecture2) :
    sourceRegion (fun n => broadcast n eta) Nbar = thermalRegion eta (1 - eta) Nbar ∧
    sourceRegion (fun n => broadcast n eta) Nbar true = thermalRegion eta (1 - eta) Nbar := by sorry

end QAlgorithms.Papers.Independent.Next46.P32

end
