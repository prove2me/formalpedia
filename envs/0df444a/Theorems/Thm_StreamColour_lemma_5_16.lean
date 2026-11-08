-- Prove2me | Theorems.Thm_StreamColour_lemma_5_16
-- name    : StreamColour.lemma_5_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:52:56.586848+00:00
-- url     : https://prove2.me/theorems/fd752ab9-9248-46ee-a342-07be3bc6ad4e
-- title:
--   Lemma 5.16 — a matching from short palettes in a dense bipartite graph
-- statement:
--   Let $A$ be a bipartite graph with left part $L_0$ of size $r\le q\le n$ and right part $[q]$. Suppose every left vertex has degree at least $11q/20$, all but at most $q/4$ left vertices have degree at least $39q/40$, and every right vertex has degree at least $q/10$. Independently at each left vertex, retain its edges to a uniform $t$-element subset of $[q]$, where $t=\lceil C_{\mathrm{pal}}\ell^2\rceil\le q$. For sufficiently large $C_{\mathrm{pal}}$, the retained graph has a matching covering $L_0$ with probability at least $1-n^{-13}$.
--
--   This gives the distinct colours of a piece's classes, from the short sampled palettes.
--
--   Differences from the source:
--   - encoding: a matching covering $L_0$ in the retained graph → an injective $f:L_0\to[q]$ with each $f(x)$ adjacent to $x$ in $A$ and in the sampled subset at $x$; reason: this is the same object; degree thresholds are real, the law is uniform on the product
-- source:
--   Chakraborty, Chatterjee, Kundu, Mishra, Streaming Graph Colouring Meets Molloy–Reed via Kernelization (STOC 2027 submission, preprint, sha256 31a813b319e4af3fd96deb52ecd284fc2c478368ab1d9064bb951dcc884cc105), Lemma 5.16, p.67 (PDF 69)

import Mathlib
import Definitions.Def_StreamColour_Params

namespace StreamColour

open Classical in
/-- Chakraborty, Chatterjee, Kundu, Mishra, *Streaming Graph Colouring Meets Molloy–Reed via Kernelization* (STOC 2027 submission, sha256 31a813b3…), Lemma 5.16, p.67 (PDF 69).

**Formalization Note.** The left part is `Fin r`, the right part is `Fin q`, and `A` is the edge relation. A matching covering `L₀` that uses
only retained edges is an injective `f` with `A x (f x)` and `f x ∈ P x`. The degree thresholds `11q/20`, `39q/40`, `q/10`, `q/4` are real.
`C₀` is absolute, before `n, q, r, A`. -/
theorem lemma_5_16 : ∃ C₀ : ℝ, ∀ Cp ≥ C₀, ∀ (n q r : ℕ) (A : Fin r → Fin q → Prop),
    r ≤ q → q ≤ n →
    (∀ x, (11 : ℝ) * q / 20 ≤ ((Finset.univ.filter (A x)).card : ℝ)) →
    (((Finset.univ.filter fun x => ((Finset.univ.filter (A x)).card : ℝ) < (39 : ℝ) * q / 40).card : ℝ)
      ≤ (q : ℝ) / 4) →
    (∀ c, (q : ℝ) / 10 ≤ ((Finset.univ.filter fun x => A x c).card : ℝ)) →
    sampleSize Cp n ≤ q →
    1 - 1 / (n : ℝ) ^ 13 ≤ unifProb (Fin r → TSubset q (sampleSize Cp n))
      (fun P => ∃ f : Fin r → Fin q, Function.Injective f ∧ ∀ x, A x (f x) ∧ f x ∈ (P x).1) := by sorry

end StreamColour
