-- Prove2me | Theorems.Thm_PettisIntegral_pettisIntegrable_of_reflexive
-- name    : PettisIntegral.pettisIntegrable_of_reflexive
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:36.753947+00:00
-- url     : https://prove2.me/theorems/0e4abb68-c406-450f-84f3-3d09fa6b75dd
-- title:
--   Lemma C.4.3.7 — weakly integrable functions with values in a reflexive Banach space are Pettis integrable
-- statement:
--   **Weak integrability implies Pettis integrability in reflexive Banach spaces (Lemma C.4.3.7).** Let $B$ be a reflexive Banach space over $\mathbb k\in\{\mathbb R,\mathbb C\}$, with dual $B'$, let $(X,\mu)$ be a measure space and let $f\colon X\to B$ be a weakly $\mu$-integrable function: $\varphi\circ f$ is $\mu$-measurable and $\mu$-integrable for every $\varphi\in B'$. Then $f$ is $\mu$-integrable in the sense of Pettis: there is $b\in B$ with
--   $$\varphi(b)=\int_X\varphi(f(x))\,d\mu(x)\qquad\text{for all }\varphi\in B'.$$
--
--   Next to quasi-completeness for continuous compactly supported functions, this is the second integrability criterion of the paper, where it is applied to the Hilbert-space valued functions $x\mapsto g(x)u$ obtained from an operator-valued function $g$ by evaluation at vectors $u$ (Lemma C.4.3.11).
--
--   **Formalization Note.** `WeaklyIntegrable` and `PettisIntegrable` are from `Def_PettisIntegral_Basic`. Reflexivity is expressed by surjectivity of the canonical map into the bidual, `NormedSpace.inclusionInDoubleDual 𝕜 B`. The statement does not involve a topology on $X$ and is given for an arbitrary positive measure space, without any finiteness assumption on $\mu$ (none is needed); the source has $X$ locally compact Hausdorff, $\mu$ a finite complex Radon measure and $\mathbb k=\mathbb C$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 714, Lemma C.4.3.7; classical reference: J. Diestel and J. J. Uhl, Jr., Vector Measures, AMS, Providence, Rhode Island, 1977, Ch. II, §3, Lemma 1 (cited in the paper's proof for the continuity of the weak integral on the dual)

import Mathlib
import Definitions.Def_PettisIntegral_Basic

open MeasureTheory

set_option autoImplicit false

namespace PettisIntegral

/-- A weakly integrable function with values in a reflexive Banach space is Pettis integrable. -/
theorem pettisIntegrable_of_reflexive {𝕜 B X : Type*} [RCLike 𝕜] [NormedAddCommGroup B]
    [NormedSpace 𝕜 B] [CompleteSpace B]
    (hB : Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 B))
    [MeasurableSpace X] (μ : Measure X) (f : X → B) (hf : WeaklyIntegrable 𝕜 μ f) :
    PettisIntegrable 𝕜 μ f := by sorry

end PettisIntegral
