-- Prove2me | Theorems.Thm_TarskiQuasiFPT_UpperBound_Supplement_lemma_14
-- name    : TarskiQuasiFPT.UpperBound.Supplement.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:30:18.183183+00:00
-- url     : https://prove2.me/theorems/0dbef1ff-6aa3-4f25-b0b3-cd43b1d1de63
-- title:
--   Lemma 14 — $G_H$ has the unique fixed point $(P_H,\overline{P_H})$
-- statement:
--   Let $H:[n]^k\to[n]^k$ have the unique fixed point $P_H$. For $z\in[n]^k$ write $\bar z=(n+1)\mathbf 1-z$, and let $G_H(x,u)=(H(x),\overline{H(\bar u)})$ on $[n]^{2k}$ (eq. (5)). Then for all $x,u\in[n]^k$,
--   $$G_H(x,u)=(x,u)\iff x=P_H\ \text{and}\ u=\overline{P_H}.$$
--
--   The lemma places every candidate fixed point of $G_H$ in the anti-chain $C=\{(z,\bar z)\}$, which does not depend on $H$. The amplification step relies on this. No monotonicity is assumed.
--
--   **Formalization Note** "$P_H$ is the unique fixed point of $H$" is the hypothesis $\forall x,\ H(x)=x\iff x=P_H$. The space $[n]^{2k}$ is the pair type with the product order.
--
--   Differences from the source:
--   - encoding: [n] = {1,…,n}, points of [n]^k ordered coordinatewise → Point n k = Fin k → Fin n (0-based values) with the pointwise order; reason: shift by one; same order, same instances
--   - encoding: [n]^{2k} and the point (x, u) → Point n k × Point n k; reason: concatenation of two k-vectors; same order
--   - encoding: P_H the unique fixed point of H → hypothesis ∀ x, H x = x ↔ x = P; reason: states exactly that P is the unique fixed point
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, Lemma 14, PDF p. 16 (printed p. 15), eq. (5)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid
import Definitions.Def_TarskiQuasiFPT_UpperBound_Supplement_LowerBound

open QAlgorithms
set_option autoImplicit false

namespace TarskiQuasiFPT.UpperBound.Supplement

/-- Lemma 14, PDF p. 16: if `P` is the unique fixed point of `H : [n]^k → [n]^k`, then for all
`x, u ∈ [n]^k`, `G_H(x, u) = (x, u)` if and only if `x = P` and `u = \overline{P}`. -/
theorem lemma_14 {n k : ℕ} (H : Point n k → Point n k) (P : Point n k)
    (hP : ∀ x, H x = x ↔ x = P) (x u : Point n k) :
    G H (x, u) = (x, u) ↔ x = P ∧ u = complement P := by sorry

end TarskiQuasiFPT.UpperBound.Supplement
