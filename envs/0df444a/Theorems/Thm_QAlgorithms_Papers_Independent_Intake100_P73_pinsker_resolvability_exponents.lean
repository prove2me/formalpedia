-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P73_pinsker_resolvability_exponents
-- name    : QAlgorithms.Papers.Independent.Intake100.P73.pinsker_resolvability_exponents
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:57:16.669991+00:00
-- url     : https://prove2.me/theorems/a3649010-55c8-471e-9e1d-957420885711
-- title:
--   Pinsker comparisons and the two resulting exponent lower bounds
-- statement:
--   Let $W:x\mapsto W_x$ be a classical discrete stochastic channel from $X$ to $Y$, and let $p$ be a probability mass function on $X$. Write $W_p(y)=\sum_xp(x)W_x(y)$. All logarithms are natural, $d(P,Q)=\sum_y|P(y)-Q(y)|$ is the full L1 distance, and $D(P\|Q)$ is extended nonnegative KL divergence, infinite on a support mismatch. Zero-mass terms in the defining KL expression contribute zero. Assume $Y$ is finite and $R\ge0$.
--
--   Define $\phi(t\mid W,p)=\log\sum_y(\sum_xp(x)W_x(y)^{1/(1+t)})^{1+t}$ and $\psi(s\mid W,p)=\log\sum_y(\sum_xp(x)W_x(y)^{1+s})W_p(y)^{-s}$, with zero-mixture terms excluded. Both functions have value zero at parameter zero. Write
--   $$
--   F_p(R)=\sup_{-1/2\le t\le0}\{-\phi(t\mid W,p)-tR\},\qquad
--   G_p(R)=\sup_{0\le s\le1}\frac{-\psi(s\mid W,p)+sR}{1+s}.
--   $$
--
--   For the worst-input bounds define $\psi_*(s\mid W)=\log\sup_p\sum_y(\sum_xp(x)W_x(y)^{1+s})^{1-s}$, retaining the source's unusual exponent $1-s$, and set
--   $$
--   G_*(R)=\sup_{0\le s\le1}\frac{-\psi_*(s\mid W)+sR}{1+s},\qquad
--   F_*(R)=\sup_{-1/2\le t\le0}\{-\sup_p\phi(t\mid W,p)-tR\}.
--   $$
--   All extrema are numerical suprema; no maximizing input law is asserted.
--
--   For the memoryless channel $W^n$ and iid reference $p^n$, let $e_\epsilon(R\mid W,p)$ and $e_D(R\mid W,p)$ be the suprema, over actual nonempty tuple codebook sequences with $\limsup_n n^{-1}\log|\Psi_n|\le R$, of the liminf normalized negative logarithm of their full L1 and KL errors relative to $W_{p^n}^n$, respectively. Repetitions in a codebook are allowed. For the worst-input versions $e_\epsilon(R\mid W)$ and $e_D(R\mid W)$, take the liminf exponent of the supremum over all block input laws of the infimum over actual tuple codes of size at most $\lceil e^{nR}\rceil$. These block input laws and codebooks need not be iid. Exact zero error gives exponent $+\infty$.
--
--   The exponent comparisons and resulting bounds are
--   $$
--   \tfrac12e_D(R\mid W,p)\le e_\epsilon(R\mid W,p),\qquad
--   \tfrac12e_D(R\mid W)\le e_\epsilon(R\mid W),
--   $$
--   $$
--   e_\epsilon(R\mid W,p)\ge\tfrac12 F_p(R),\qquad
--   e_\epsilon(R\mid W)\ge\tfrac12 F_*(R).
--   $$
--   These are the source's (40)–(41) and preceding comparisons. With full L1 and nats, the background Pinsker inequality is $D\ge d^2/2$; the source omits this factor. A fixed multiplicative error constant vanishes after taking a normalized logarithm, so the exponent statements are unchanged.
-- source:
--   General non-asymptotic and asymptotic formulas in channel resolvability and identification capacity and their application to wire-tap channel, arXiv:cs/0503088v2, PDF p. 10, Unnumbered (40)–(41): Pinsker-derived L1 exponent bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P73

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P73

open Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

/-- Hayashi, PDF p.10, (40)–(41), plus the preceding exponent comparisons.
SOURCE CORRECTION: full-L1/nats Pinsker is D>=L1^2/2, not D>=L1^2.
The fixed factor disappears in normalized negative logs, leaving (40)–(41) unchanged. -/
theorem pinsker_resolvability_exponents {X Y : Type*} [Nonempty X] [Finite Y]
    (W : X → Y → ℝ≥0∞) (hW : IsDiscreteStochastic W) (p : PMF X) (R : ℝ) (hR : 0 ≤ R) :
    fixedResolvabilityExponent true W p R / 2 ≤ fixedResolvabilityExponent false W p R ∧
    worstExponent true W R / 2 ≤ worstExponent false W R ∧
    phiExponent W p R / 2 ≤ fixedResolvabilityExponent false W p R ∧
    worstPhiExponent W R / 2 ≤ worstExponent false W R := by sorry

end QAlgorithms.Papers.Independent.Intake100.P73

end
