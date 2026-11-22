-- Prove2me | Theorems.Thm_SchwartzDist_dense_setOf_hasCompactSupport
-- name    : SchwartzDist.dense_setOf_hasCompactSupport
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:34:40.820612+00:00
-- url     : https://prove2.me/theorems/8927e74a-6a44-482d-bb73-a79564163c30
-- title:
--   Compactly supported smooth functions are dense in the Schwartz space $\mathcal S(E,F)$
-- statement:
--   **Density of test functions in the Schwartz space.** Let $E$ be a finite-dimensional real normed space (for instance $E=\mathbb R^n$) and let $F$ be a real normed space. Let $\mathcal S(E,F)$ be the Schwartz space of smooth functions $f:E\to F$ all of whose derivatives decay faster than any power of $\|x\|$, with its locally convex topology (a Fréchet topology when $F$ is complete) given by the seminorms
--   $$p_{k,n}(f)=\sup_{x\in E}\|x\|^{k}\,\big\|D^{n}f(x)\big\|\qquad(k,n\ge 0).$$
--   Every smooth function with compact support is a Schwartz function, and the subspace $C_c^\infty(E,F)$ of compactly supported ones is dense:
--   $$\overline{\{f\in\mathcal S(E,F)\;:\;\operatorname{supp}f\ \text{is compact}\}}=\mathcal S(E,F).$$
--
--   This is the classical density $C_c^\infty(\mathbb R^n)\subset\mathcal S(\mathbb R^n)$. Its standard consequence is that the transpose of the inclusion $\mathcal D(\mathbb R^n)\to\mathcal S(\mathbb R^n)$ is injective, so that tempered distributions are distributions. The paper uses it in this way in the proof of Theorem 5.3.2.1 (p. 244), and again on p. 247 in the proof of Theorem 5.3.2.5, to extend an identity from $\mathcal D(\mathbf R^2)$ to $\mathcal S(\mathbf R^2)$.
--
--   **Formalization Note.** `𝓢(E, F)` is Mathlib's `SchwartzMap` with its seminorm topology, and compact support is `HasCompactSupport`. The source states the result for complex-valued functions on $\mathbf R^m$. Here $E$ is any finite-dimensional real normed space and $F$ any real normed space, not necessarily complete.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 244, proof of Theorem 5.3.2.1 ("denseness of $\mathcal D(\mathbf R)\subset\mathcal S(\mathbf R)$"), and p. 247, proof of Theorem 5.3.2.5; classical reference: L. Hörmander, The Analysis of Linear Partial Differential Operators I, Springer-Verlag, 1983, Ch. VII, Lemma 7.1.8, p. 163 (as cited by the paper)

import Mathlib

open SchwartzMap LineDeriv Topology Filter

set_option autoImplicit false

namespace SchwartzDist

theorem dense_setOf_hasCompactSupport
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Dense {f : 𝓢(E, F) | HasCompactSupport (f : E → F)} := by sorry

end SchwartzDist
