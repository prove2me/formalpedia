-- Prove2me | Theorems.Thm_PettisIntegral_hasPettisIntegral_integral
-- name    : PettisIntegral.hasPettisIntegral_integral
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:45.240505+00:00
-- url     : https://prove2.me/theorems/8a6c9994-60e5-4c4a-a82b-e97ca84f3731
-- title:
--   Remark C.4.2.2 — a Bochner integrable Banach-space-valued function is Pettis integrable, with the same integral
-- statement:
--   **Bochner integrable functions are Pettis integrable, with the same integral (Remark C.4.2.2).** Let $E$ be a Banach space over $\mathbb k\in\{\mathbb R,\mathbb C\}$, let $(X,\mu)$ be a measure space with $\mu$ a positive measure, and let $f\colon X\to E$ be integrable in the sense of Bochner. Then $f$ is $\mu$-integrable in the sense of Pettis and its Pettis integral is its Bochner integral:
--
--   1. for every continuous linear form $\varphi\in E'$, the function $\varphi\circ f$ is $\mu$-integrable and
--   $$\varphi\Bigl(\int_X f\,d\mu\Bigr)=\int_X\varphi(f(x))\,d\mu(x),$$
--   where $\int_X f\,d\mu\in E$ on the left is the Bochner integral;
--   2. the Pettis integral of $f$ (the unique vector of $E$ representing the weak integral) equals the Bochner integral $\int_X f\,d\mu$.
--
--   This holds because the formation of the Bochner integral commutes with continuous linear maps. It is the bridge between the two theories of vector-valued integration: every statement about Pettis integrals applies to Bochner integrals. (The converse fails: a Pettis integrable function with values in a separable Hilbert space need not be Bochner integrable.)
--
--   **Formalization Note.** `HasPettisIntegral 𝕜 μ f a` and `pettisIntegral 𝕜 μ f` are the notions of `Def_PettisIntegral_Basic`; `Integrable f μ` and `∫ x, f x ∂μ` are Mathlib's Bochner integrability and Bochner integral. The space `E` carries `[NormedSpace 𝕜 E]` and, as Mathlib's Bochner integral requires, `[NormedSpace ℝ E]` (a real normed space structure on a normed group is unique, so it is the restriction of scalars of the `𝕜`-structure), and `[CompleteSpace E]` (without completeness Mathlib's integral is the junk value $0$). The statement is given on an arbitrary measure space (the source: $X$ locally compact Hausdorff, $\mu$ a Radon measure, $\mathbb k=\mathbb C$). **Deviation from the source.** Only the first assertion of the remark is formalized; its further claim that the two integrals coincide for continuous weakly integrable functions with values in a separable Banach space is false as a statement about Bochner integrability and is omitted.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 710, Remark C.4.2.2 (first part); for Bochner's theory the paper refers to S. Lang, Real and Functional Analysis, Third Edition, Springer, Ch. VI

import Mathlib
import Definitions.Def_PettisIntegral_Basic

open MeasureTheory

set_option autoImplicit false

namespace PettisIntegral

/-- A Bochner integrable function with values in a Banach space is Pettis integrable, and its
Pettis integral is its Bochner integral. -/
theorem hasPettisIntegral_integral {𝕜 E X : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace X] (μ : Measure X)
    (f : X → E) (hf : Integrable f μ) :
    HasPettisIntegral 𝕜 μ f (∫ x, f x ∂μ) ∧ pettisIntegral 𝕜 μ f = ∫ x, f x ∂μ := by sorry

end PettisIntegral
