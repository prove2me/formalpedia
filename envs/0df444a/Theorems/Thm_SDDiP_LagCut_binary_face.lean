-- Prove2me | Theorems.Thm_SDDiP_LagCut_binary_face
-- name    : SDDiP.LagCut.binary_face
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:46:12.960625+00:00
-- url     : https://prove2.me/theorems/76180019-aa5e-4237-82d7-1e69c42a6111
-- title:
--   Proof of Theorem 3, p. 479 — at a binary $\hat x$, $\mathrm{conv}(X''_n) \cap \{z_n=\hat x\} = \mathrm{conv}(X''_n \cap \{z_n = \hat x\})$
-- statement:
--   Let $n$ be a node in iteration $i$, with $X''_n$ the set of quadruples $(z,x,y,\theta)$ of (4.4); every point of $X''_n$ has $z \in [0,1]^d$. Let $\hat x \in \{0,1\}^d$ be a binary parent state. Then
--
--   $$\mathrm{conv}(X''_n) \cap \{ z_n = \hat x\} = \mathrm{conv}\big(X''_n \cap \{z_n = \hat x\}\big).$$
--
--   In words: a convex combination of points of $X''_n$ whose $z$-part equals the binary vector $\hat x$ only uses points whose $z$-part is already $\hat x$. This is the step of the proof of Theorem 3 where the redundant constraint $z_n \in [0,1]^d$ of (2.1c) and the binarity of the state are used; it turns the convexified problem (4.5) into a convexification of the forward problem itself.
--
--   **Formalization Note** The inclusion $\supseteq$ is immediate; the content is $\subseteq$, which is the step the paper proves. Points are tuples `(z, x, y, θ)` and the face is `{p | p.1 = x̂}`.
-- source:
--   Zou, Ahmed, Sun, Stochastic dual dynamic integer programming, Math. Program. 175 (2019), p. 479, proof of Theorem 3 (paragraph after (4.5))

import Mathlib
import Definitions.Def_SDDiP_LagCut_Node

namespace SDDiP.LagCut

open Node

/-- Proof of Theorem 3, p. 479 (Zou, Ahmed, Sun, Math. Program. 175 (2019)): for a binary parent
state `x̂ ∈ {0,1}ᵈ`, the points of `conv(X″_n)` with `z = x̂` are exactly the convex combinations of
points of `X″_n` with `z = x̂`: `conv(X″_n) ∩ {z = x̂} = conv(X″_n ∩ {z = x̂})`. -/
theorem binary_face {d l : ℕ} (N : Node d l) (xhat : Fin d → ℝ) (hxhat : IsBinary xhat) :
    convexHull ℝ N.X'' ∩ {p | p.1 = xhat} = convexHull ℝ (N.X'' ∩ {p | p.1 = xhat}) := by sorry

end SDDiP.LagCut
