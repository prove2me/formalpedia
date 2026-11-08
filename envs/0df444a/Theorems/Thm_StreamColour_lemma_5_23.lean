-- Prove2me | Theorems.Thm_StreamColour_lemma_5_23
-- name    : StreamColour.lemma_5_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:54:32.167271+00:00
-- url     : https://prove2.me/theorems/a01a183d-5a5e-4b0f-a559-aed0a4de69b8
-- title:
--   Lemma 5.23 — with probability $1-n^{-12}$ every near piece has a matching anchored in $\mathcal R^\star$
-- statement:
--   Let $G$ be a graph on $n$ vertices of maximum degree at most $\Delta$, with a partition into pieces. Let $A\ge0$, $K_{\mathrm{rec}}\ge\max\{3000,3(A+1)\}$, $h\ge\ell$, $L=100h$, and $b_0=K_{\mathrm{rec}}h<n$. With probability at least $1-n^{-12}$ over the independent capacities, simultaneously every near piece $C$ admits one of the following:
--
--   1. a complement matching with $L$ pairs, each having an endpoint in $\mathcal R^\star$; or
--   2. a maximal complement matching with fewer than $L$ pairs, all of whose unmatched vertices belong to $\mathcal R^\star$.
--
--   The matchings depend only on the graph, the partition and the capacities: no colour sample enters the statement.
--
--   Differences from the source:
--   - generalization: a decomposition satisfying Definition 5.1 of a graph promised $(\Delta-k)$-colourable with $1\le k<\Delta\le n-1$, $h=\lceil C(k+\ell^{10})\rceil$, and $K_{\mathrm{rec}}\ge\max\{3000,3(A+1),8c_X+3\}$ → any labelling $\pi$ of any graph of maximum degree at most $\Delta$, any integer $h\ge\ell$, and $K_{\mathrm{rec}}\ge\max\{3000,3(A+1)\}$; reason: the proof uses only that the pieces are disjoint, that $C$ is near, the degree bound, and these inequalities; the paper's case is a special case
--   - encoding: "can be chosen using only the graph, decomposition, and capacities, independently of all colour samples" → the event is a property of $G,\pi,b$, with no colour sample in it; reason: it holds by construction
--   - encoding: $L=\lceil100h\rceil$, and "with probability" over capacities → $L=100h$, and a measurable event of measure at least $1-n^{-12}$ under the product of capacity laws; reason: $h$ is an integer; the inner bound as in the goal
-- source:
--   Chakraborty, Chatterjee, Kundu, Mishra, Streaming Graph Colouring Meets Molloy–Reed via Kernelization (STOC 2027 submission, preprint, sha256 31a813b319e4af3fd96deb52ecd284fc2c478368ab1d9064bb951dcc884cc105), Lemma 5.23, pp.79–80 (PDF 81–82); §5.10, p.76 (PDF 78); Step 1, p.75 (PDF 77)

import Mathlib
import Definitions.Def_StreamColour_Params
import Definitions.Def_StreamColour_Capacity

namespace StreamColour

/-- Chakraborty, Chatterjee, Kundu, Mishra, *Streaming Graph Colouring Meets Molloy–Reed via Kernelization* (STOC 2027 submission, sha256 31a813b3…), Lemma 5.23, pp.79–80 (PDF 81–82), with the capacities of Step 1, p.75, and the constants of §5.10, p.76.

**Formalization Note.** The proof uses only that the pieces are disjoint (they are the fibres of `π`) and the near condition (8), so `π` may be any labelling:
this is more general than "a decomposition satisfying Definition 5.1", which is a special case. From §5.10: `L = 100h`, `b₀ = K_rec h < n`, `K_rec ≥ 3000`, `K_rec ≥ 3(A+1)`, `h ≥ ℓ`. The last
sentence of the lemma holds by construction: the event `AnchoredMatchings` is about `G`, `π`, `b` alone, and no colour sample occurs in it. -/
theorem lemma_5_23 (A : ℝ) (Krec h n Δ : ℕ) (G : SimpleGraph (Fin n)) (π : Fin n → ℕ)
    (hA : 0 ≤ A) (hK : 3000 ≤ Krec) (hK' : 3 * (A + 1) ≤ (Krec : ℝ)) (hh : ell n ≤ h)
    (hb₀ : Krec * h < n) (hdeg : ∀ v, (G.neighborSet v).ncard ≤ Δ) :
    ProbAtLeast (capacityMeasure n (Krec * h)) {b | AnchoredMatchings A h Δ G π b}
      (ENNReal.ofReal (1 - 1 / (n : ℝ) ^ 12)) := by sorry

end StreamColour
