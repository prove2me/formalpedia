-- Prove2me | Theorems.Thm_PsiPhi_halfPlaneOrderHomeomorph_exists
-- name    : PsiPhi.halfPlaneOrderHomeomorph_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T09:50:19.653075+00:00
-- url     : https://prove2.me/theorems/71bce77a-623e-4e56-aa19-435ebc5644e2
-- title:
--   Existence of the reparameterisation of the half-line onto the real line
-- statement:
--   Let $n$ be a natural number. The open half-line $\{x \in \mathbb{R} : x < n+1\}$ carries the usual order topology, and it is homeomorphic to all of $\mathbb{R}$ in a way that is explicit about the branch point $n$.
--
--   The map $\psi_n$ is the piecewise function
--   $$\psi_n(x) = x \text{ for } x \le n, \qquad \psi_n(x) = n + \frac{x-n}{n+1-x} \text{ for } n < x < n+1.$$
--   Thus $\psi_n$ is the **identity** on the whole ray $(-\infty, n]$, and on the short interval $(n, n+1)$ it is a strictly increasing bijection onto $(n, \infty)$. Writing $u = x-n \in (0,1)$, the second branch sends $u$ to $u/(1-u)$, so it stretches the bounded interval $(n,n+1)$ onto the unbounded ray $(n,\infty)$ and blows up as $x \to n+1^{-}$.
--
--   The inverse $\varphi_n : \mathbb{R} \to \{x : x < n+1\}$ is again explicit:
--   $$\varphi_n(y) = y \text{ for } y \le n, \qquad \varphi_n(y) = n + \frac{y-n}{1+y-n} \text{ for } y > n.$$
--   On the second branch, writing $v = y-n > 0$, the formula is $v \mapsto v/(1+v)$, the literal algebraic inverse of $u \mapsto u/(1-u)$. The two round trips $\varphi_n(\psi_n(x)) = x$ (for $x<n+1$) and $\psi_n(\varphi_n(y))=y$ (for all $y$) both hold, so surjectivity is immediate and no separate existence-of-preimage argument is required.
--
--   Continuity is the one genuinely delicate point. $\psi_n$ is *not* continuous on all of $\mathbb{R}$: its second branch has a pole at the boundary point $x=n+1$, exactly where $\psi_n$ ceases to be defined. The correct statement is continuity on the half-line $\{x : x<n+1\}$, and it follows from the pasting lemma for piecewise-continuous functions: the two branches are continuous on the closed sets $\{x\le n\}$ and $\{x\ge n\}$ and agree at the unique overlap point $x=n$, where both give $n$.
--
--   By contrast $\varphi_n$ *is* continuous on all of $\mathbb{R}$, even though its second branch appears to have a pole at $y=n-1$. That pole is harmless because $n-1\le n$, so it lies inside the region where the *first* branch is selected and never appears in the function actually evaluated. Formally, on the closed ray $\{y\ge n\}$ the denominator $1+y-n$ satisfies $1+y-n\ge 1>0$, so the second branch is a continuous rational function there, and pasting gives continuity everywhere.
--
--   Two identities make this homeomorphism useful for braids: $\psi_n$ is the **identity** at every point $k+1$ with $0\le k<n$, i.e. $\psi_n(k+1)=k+1$; and $\psi_n(n+\tfrac12)=n+1$. The first says the reparameterisation fixes each of the punctures $1,2,\dots,n$ of a punctured plane exactly, which is what allows it to descend to a homeomorphism of punctured spaces and to carry standard loops to standard loops. The second pins a convenient base point: the point $n+\tfrac12$, which lies strictly inside the half-line, is carried to the boundary value $n+1$.
-- source:
--   Auxiliary order homeomorphism introduced for BraidsLinksMCG.puncturedPlane_succ_left_factor_homeomorph_v1. The construction is the standard order-isomorphism stretching $(n,n+1)$ onto $(n,\infty)$; the explicit inverse is required because it turns surjectivity into two algebraic round trips.

import Mathlib
import Definitions.Def_PsiPhi

namespace PsiPhi

theorem halfPlaneOrderHomeomorph_exists (n : ℕ) :
    Nonempty ({x : ℝ // x < (n : ℝ) + 1} ≃ₜ ℝ) := by sorry

end PsiPhi
