-- Prove2me | Theorems.Thm_StreamColour_lemma_4_3
-- name    : StreamColour.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:52:51.271213+00:00
-- url     : https://prove2.me/theorems/f4ca44dc-7c6c-4998-8fac-29b46bd7ac58
-- title:
--   Lemma 4.3 — every vertex of the kernel has many nonadjacent neighbour pairs or many higher-degree neighbours
-- statement:
--   Let $H$ be the graph remaining after the reduction rules, with $h\ge1$, and write $d_v=d_H(v)$. For every $v\in V(H)$ we have $d_v>20h$, and at least one of the following holds:
--
--   1. $M_v\ge hd_v/8$, where $M_v=\binom{d_v}{2}-|E(H[N_H(v)])|$;
--   2. at least $d_v/4$ neighbours $u$ of $v$ satisfy $d_H(u)>d_v+h$.
--
--   These two alternatives are the sources of colour savings in the colouring argument for $H$.
--
--   Differences from the source:
--   - generalization: the setting of §4 (maximum degree at most $\Delta$, $\Delta>40h$, $G$ promised $(\Delta-k)$-colourable, $h=\lceil C(k+\ell^{10})\rceil$) → any graph on $[n]$ and any integer $h\ge1$; reason: the proof uses only that neither reduction rule applies to $H$; the paper's setting is a special case
--   - encoding: the graph $H$ of §4.1 → the remainder computed by the rules, with $h\ge1$ as in Lemma 4.2; reason: $H$ is defined there; both thresholds stay real, with no floor
-- source:
--   Chakraborty, Chatterjee, Kundu, Mishra, Streaming Graph Colouring Meets Molloy–Reed via Kernelization (STOC 2027 submission, preprint, sha256 31a813b319e4af3fd96deb52ecd284fc2c478368ab1d9064bb951dcc884cc105), Lemma 4.3, p.25 (PDF 27)

import Mathlib
import Definitions.Def_StreamColour_Reduction

namespace StreamColour

/-- Chakraborty, Chatterjee, Kundu, Mishra, *Streaming Graph Colouring Meets Molloy–Reed via Kernelization* (STOC 2027 submission, sha256 31a813b3…), Lemma 4.3, p.25 (PDF 27).

Every vertex `v` of the remainder `H` has `d_v > 20h`, and `M_v ≥ h d_v / 8` or at least `d_v / 4` neighbours `u` of `v`
satisfy `d_H(u) > d_v + h`.

**Formalization Note.** Both thresholds are real, with no floor. `h ≥ 1` is the standing assumption of Lemma 4.2. -/
theorem lemma_4_3 (n h : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hh : 1 ≤ h)
    (v : Fin n) (hv : v ∈ remainder G h) :
    20 * h < liveDeg G (remainder G h) v ∧
    ((h : ℝ) * (liveDeg G (remainder G h) v : ℝ) / 8 ≤ deficitM G (remainder G h) v ∨
      (liveDeg G (remainder G h) v : ℝ) / 4 ≤
        (((liveNbrs G (remainder G h) v).filter fun u =>
          liveDeg G (remainder G h) v + h < liveDeg G (remainder G h) u).card : ℝ)) := by sorry

end StreamColour
