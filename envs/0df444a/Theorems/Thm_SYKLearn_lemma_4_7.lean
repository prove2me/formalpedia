-- Prove2me | Theorems.Thm_SYKLearn_lemma_4_7
-- name    : SYKLearn.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:15:52.785868+00:00
-- url     : https://prove2.me/theorems/52cc6b4d-66d6-4e9c-a09b-2b86ee82624a
-- title:
--   Lemma 4.7 — state distance: $\|\hat\rho-\rho\|_1\le\beta\|\hat H-H\|$
-- statement:
--   Let $H,\hat H$ be Hermitian matrices, $\beta>0$, and let
--
--   $$\rho=\frac{e^{-\beta H}}{\mathrm{tr}[e^{-\beta H}]},\qquad \hat\rho=\frac{e^{-\beta\hat H}}{\mathrm{tr}[e^{-\beta\hat H}]},\qquad \Delta=\hat H-H.$$
--
--   Then
--
--   $$\|\hat\rho-\rho\|_1\le\beta\|\Delta\| ,$$
--
--   with $\|\cdot\|_1$ the trace norm and $\|\cdot\|$ the operator norm.
--
--   The bound controls how much the scale experiment changes when it is run on the true Gibbs state instead of the Gibbs state of the learned Hamiltonian.
--
--   **Formalization Note** The paper states the bound for normalized-trace states and the normalized trace norm, which is the ordinary trace norm of the physical states used here.
--
--   Differences from the source:
--   - generalization: H, Ĥ Hamiltonians on the n-mode space ℂ^{2^{n/2}} → any Hermitian H, H′ on any finite-dimensional space; reason: the proof (quantum Pinsker) uses nothing about the dimension or the SYK structure; specializing the space gives the page's statement
--   - encoding: ‖ρ̂ − ρ‖₁ = Tr|ρ̂ − ρ| for normalized-trace states → traceNorm (gibbs H′ β − gibbs H β) of the physical states; reason: ρ = 2^{n/2}·gibbs and Tr = 2^{−n/2} tr, so the two norms agree
-- source:
--   Anshu–Arunachalam–Chen–Hwang, Efficiently Learning SYK Hamiltonians, STOC 2027 submission (held file sha256 5d7d199a…), Lemma 4.7, p.38

import Mathlib
import Definitions.Def_SYKLearn_Basic

noncomputable section
open SYKFastMix.FastMixing

namespace SYKLearn

/-- **Lemma 4.7 (State distance)**, p.38 (Anshu–Arunachalam–Chen–Hwang, *Efficiently Learning SYK
Hamiltonians*, STOC 2027 submission, held file sha256 5d7d199a…). Let
`ρ = e^{−βH}/Tr[e^{−βH}]`, `ρ̂ = e^{−βĤ}/Tr[e^{−βĤ}]`, `∆ = Ĥ − H`. Then `‖ρ̂ − ρ‖₁ ≤ β‖∆‖`.

**Formalization Note.** The paper's `‖·‖₁` is the normalized trace norm `Tr|·|` of the
normalized-trace states `ρ, ρ̂`, which equals the ordinary trace norm (`traceNorm`, sum of singular
values) of the physical states `gibbs H β`, `gibbs Ĥ β`. `‖∆‖` is the operator norm. Stated for any
Hermitian `H, Ĥ` on any finite-dimensional space and `β > 0`. -/
theorem lemma_4_7 {ι : Type} [Fintype ι] [DecidableEq ι] (H H' : Mat ι) (hH : H.IsHermitian)
    (hH' : H'.IsHermitian) (β : ℝ) (hβ : 0 < β) :
    traceNorm (gibbs H' β - gibbs H β) ≤ β * SYKEdge.opNorm (H' - H) := by sorry

end SYKLearn
