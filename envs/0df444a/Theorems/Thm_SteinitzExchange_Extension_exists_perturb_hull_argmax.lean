-- Prove2me | Theorems.Thm_SteinitzExchange_Extension_exists_perturb_hull_argmax
-- name    : SteinitzExchange.Extension.exists_perturb_hull_argmax
-- status  : Proved
-- author  : @choi
-- created : 2026-10-01T03:34:00.306484+00:00
-- url     : https://prove2.me/theorems/25152744-f810-49e1-b3e3-da1370b5c0a2
-- title:
--   Every hull point lies in the hull of maximizers of a linear perturbation
-- statement:
--   Let $V$ be a finite nonempty coordinate set, let $B\subseteq\mathbb Z^V$ be finite and nonempty, and let $g:\mathbb Z^V\to\mathbb R$. Write $P=\operatorname{conv}(B)$, with integer vectors embedded in $\mathbb R^V$. For $p\in\mathbb R^V$, define
--   $$
--   M_g(p)=\{x\in B:g(x)+\langle p,x\rangle\ge g(y)+\langle p,y\rangle\text{ for every }y\in B\}.
--   $$
--   Then every $b\in P$ satisfies
--   $$
--   \exists p\in\mathbb R^V,\qquad b\in\operatorname{conv}(M_g(p)).
--   $$
--   This describes how the upper polyhedral envelope of a finite lifted graph is covered by exposed maximizer faces. It supplies the perturbation needed to study a prescribed point, including points on the boundary of $P$. No exchange property is assumed for $B$ or $g$.
-- source:
--   Kazuo Murota, Convexity and Steinitz's Exchange Property, Advances in Mathematics 124 (1996), 272–311, DOI 10.1006/aima.1996.0084; https://scispace.com/pdf/convexity-and-steinitz-s-exchange-property-1h0w0a22vc.pdf; Section 4.1, equation (4.3), and Section 4.2, proof of Theorem 4.4, supporting-hyperplane step leading to equation (4.8). This isolates the finite polyhedral support assertion used there.

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange

namespace SteinitzExchange.Extension


theorem exists_perturb_hull_argmax {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : B.Nonempty) (g : (V → ℤ) → ℝ) (b : V → ℝ)
    (hb : b ∈ hull B) :
    ∃ p : V → ℝ, b ∈ hull (argmaxB B (perturb g p)) := by sorry

end SteinitzExchange.Extension
