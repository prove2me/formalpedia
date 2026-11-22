-- Prove2me | Theorems.Thm_SchwartzDist_exists_taylorCoeffCLM_surjective_isOpenMap
-- name    : SchwartzDist.exists_taylorCoeffCLM_surjective_isOpenMap
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:34:46.35664+00:00
-- url     : https://prove2.me/theorems/5c9b5546-50b8-485a-b98b-a94718e08e12
-- title:
--   The Taylor map $\mathcal S(\mathbb R)\to\mathbb C[[X]]$, $f\mapsto\sum_k f^{(k)}(0)X^k/k!$, is a continuous open linear surjection
-- statement:
--   **Taylor expansion at the origin identifies $\mathcal S(\mathbb R)/\mathcal S_{00}(\mathbb R)$ with $\mathbb C[[X]]$.** Identify the space of formal power series $\mathbb C[[X]]$ with $\mathbb C^{\mathbb N}$ (coefficient sequences), carrying the product topology, i.e. the Hausdorff locally convex topology of the seminorms
--   $$q_N\Big(\sum_{k\ge0}c_kX^k\Big)=\sup_{0\le k\le N}|c_k|\qquad(N\ge0).$$
--   Let $\mathcal S(\mathbb R)=\mathcal S(\mathbb R,\mathbb C)$ be the Schwartz space of smooth functions $f:\mathbb R\to\mathbb C$ all of whose derivatives decay faster than any power of $|x|$, with its Fréchet topology given by the seminorms $\sup_{x\in\mathbb R}|x|^{a}\,|f^{(b)}(x)|$ ($a,b\ge0$). Let $J:\mathcal S(\mathbb R)\to\mathbb C[[X]]$ be the Taylor map at $0$,
--   $$J(f)=\sum_{k\ge0}\frac{f^{(k)}(0)}{k!}\,X^k .$$
--   Then $J$ is continuous and $\mathbb C$-linear, surjective, and open.
--
--   The kernel of $J$ is the space $\mathcal S_{00}(\mathbb R)$ of Schwartz functions flat at $0$, so $J$ induces a linear topological isomorphism $\mathcal S(\mathbb R)/\mathcal S_{00}(\mathbb R)\cong\mathbb C[[X]]$, the quotient carrying the quotient topology. This is Theorem 5.3.2.1(2) of the paper, the dual counterpart of the description of tempered distributions supported at the origin.
--
--   **Deviation from the source.** The paper writes that the isomorphism sends "each $f\in\mathcal S(\mathbf R)'_\beta$" to $\sum_k f^{(k)}(0)X^k/k!$. This is a misprint for $f\in\mathcal S(\mathbf R)$, since the map is defined on Schwartz functions. (ERRATA I140 of the upstream formalization records the same correction.)
--
--   **Formalization Note.** $\mathbb C[[X]]$ is modelled as `ℕ → ℂ` with the product topology, which is the topology of the seminorms $q_N$. The isomorphism of the quotient is stated in the equivalent form "continuous linear, surjective and open, with the displayed coefficients"; the kernel is then $\{f: f^{(k)}(0)=0\ \forall k\}=\mathcal S_{00}(\mathbb R)$ by the coefficient formula. `iteratedDeriv k f 0` is the ordinary $k$-th derivative at $0$ of the smooth function $f$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 243, Theorem 5.3.2.1(2), (5.3.2.3), with proof on p. 245

import Mathlib

open SchwartzMap LineDeriv Topology Filter

set_option autoImplicit false

namespace SchwartzDist

theorem exists_taylorCoeffCLM_surjective_isOpenMap :
    ∃ J : 𝓢(ℝ, ℂ) →L[ℂ] (ℕ → ℂ),
      (∀ (f : 𝓢(ℝ, ℂ)) (k : ℕ), J f k = iteratedDeriv k (f : ℝ → ℂ) 0 / (k.factorial : ℂ)) ∧
      Function.Surjective J ∧ IsOpenMap J := by sorry

end SchwartzDist
