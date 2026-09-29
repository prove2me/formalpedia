-- Prove2me | Theorems.Thm_PsiPhi_psi_phi_roundtrip_and_continuity_v1
-- name    : PsiPhi.psi_phi_roundtrip_and_continuity_v1
-- status  : Open
-- author  : @WillR
-- created : 2026-09-28T20:05:06.364133+00:00
-- url     : https://prove2.me/theorems/e53c27a6-3166-474c-b710-2e4974c43acd
-- title:
--   Round trips, range bounds and continuity for the half-line reparameterisation pair
-- statement:
--   Let $n$ be a natural number, and let $\psi_n$ and $\varphi_n$ be the published reparameterisation of the half-line $\{x<n+1\}$ onto $\mathbb{R}$ and its explicit inverse.
--
--   This record collects the four algebraic and analytic facts about the pair that a later complex lift needs, so that they need not be re-derived.
--
--   **Round trips.** $\varphi_n(\psi_n(x))=x$ for every $x<n+1$, and $\psi_n(\varphi_n(y))=y$ for every $y\in\mathbb{R}$. Writing $u=x-n\in(0,1)$ on the second branch of $\psi_n$, that branch sends $u\mapsto u/(1-u)$; writing $v=y-n>0$ on the second branch of $\varphi_n$, that branch sends $v\mapsto v/(1+v)$. These are literal algebraic inverses, so bijectivity follows with no separate existence-of-a-preimage argument.
--
--   **Range bounds.** Both maps land strictly below the right endpoint: $\psi_n(x)<n+1$ whenever $x<n+1$, and $\varphi_n(y)<n+1$ for every $y$. The first is the statement that the reparameterisation really is defined on its whole domain, and the second is what makes $\varphi_n$ a map into the half-line rather than merely into $\mathbb{R}$.
--
--   **Continuity of $\psi_n$ is only on the half-line.** The function $\psi_n$ is *not* continuous on all of $\mathbb{R}$: its second branch has a pole at $x=n+1$, precisely the boundary point where $\psi_n$ ceases to be defined. The correct statement, and the one proved here, is that $\psi_n$ is continuous on $\{x:x<n+1\}$.
--
--   **Continuity of $\varphi_n$ is global.** $\varphi_n$ *is* continuous on all of $\mathbb{R}$, even though its second branch appears to have a pole at $y=n-1$. That pole is harmless because $n-1\le n$, so it lies inside the region where the *first* branch is selected and is never evaluated. Formally, on the closed ray $\{y\ge n\}$ the denominator $1+y-n$ satisfies $1+y-n\ge 1>0$, so the second branch is a continuous rational function there, and pasting gives continuity everywhere.
--
--   The two continuity statements use the pasting lemma for piecewise-continuous functions, with the branches continuous on the closed sets $\{x\le n\}$ and $\{x\ge n\}$; both branches agree at the unique overlap point $x=n$, where each gives $n$.
-- source:
--   Auxiliary record for BraidsLinksMCG.puncturedPlane_succ_left_factor_homeomorph_v1. The Proved target PsiPhi.halfPlaneOrderHomeomorph_exists only states Nonempty, so its solution exports none of the round-trip or continuity arguments; they are re-proved here in one reusable place rather than inside the complex-lift parent. Every proof here is the argument already remotely accepted for 71bce77a, with psi_lt added as its mirror image.

import Mathlib
import Definitions.Def_PsiPhi

namespace PsiPhi

theorem psi_phi_roundtrip_and_continuity_v1 (n : ℕ)
    (x : {x : ℝ // x < (n : ℝ) + 1}) (y : ℝ) :
    phi n (psi n x.1) = x.1 ∧
      psi n (phi n y) = y ∧
      psi n x.1 < (n : ℝ) + 1 ∧
      phi n y < (n : ℝ) + 1 ∧
      ContinuousOn (psi n) (Set.Iio ((n : ℝ) + 1)) ∧
      Continuous (phi n) := by sorry

end PsiPhi
