-- Prove2me | Theorems.Thm_StreamColour_lemma_4_12
-- name    : StreamColour.lemma_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:54:01.454877+00:00
-- url     : https://prove2.me/theorems/ab939fe8-0eb1-4f40-944c-ede44ed3cbbf
-- title:
--   Lemma 4.12 — with probability $9/10$ the sampled palettes contain a proper colouring of the kernel
-- statement:
--   Let $1\le k<\Delta\le n-1$ and $q=\Delta-k$, let $G$ be an $n$-vertex $q$-colourable graph of maximum degree at most $\Delta$ with $\Delta>40h$, let $H$ be the graph remaining after the reduction rules, and let $L(v)$ be the lists defined from any proper $q$-colouring of $G[K]$. Sample independently the priorities and the two ordered colour arrays at each vertex. For sufficiently large $C$ and $C_{\mathrm{A,pal}}$, with probability at least $9/10$ there is a proper colouring $\chi$ of $H$ with
--
--   $$\chi(v)\in L(v)\cap Q_v(D_v)\qquad(v\in V(H)),$$
--
--   where $D_v$ is the power of two with $D_v\le d_v+1<2D_v$.
--
--   This is the existence statement behind Algorithm A: short adaptive palettes, whose lengths are fixed before the stream, suffice for the kernel.
--
--   Differences from the source:
--   - encoding: priorities and arrays on $V(H)$, as printed → one priority and two arrays at every vertex of $G$ (§4.3, p.37), uniform on the finite product; reason: the event reads coordinates of $V(H)$ only, so the probability is the same
--   - reading: "for sufficiently large $C_{\mathrm{A,pal}}$" → thresholds $C_0$ and $C_{p,0}$ before $n,\Delta,k,G$, with every $C\ge C_0$ and $C_{\mathrm{A,pal}}\ge C_{p,0}$; reason: the lemma calls $C_{\mathrm{A,pal}}$ absolute (p.38); §6 needs $C$ free above a threshold; $h\ge2k+2$ of p.23 comes from $C$ large
-- source:
--   Chakraborty, Chatterjee, Kundu, Mishra, Streaming Graph Colouring Meets Molloy–Reed via Kernelization (STOC 2027 submission, preprint, sha256 31a813b319e4af3fd96deb52ecd284fc2c478368ab1d9064bb951dcc884cc105), Lemma 4.12, p.38 (PDF 40); §4.2, p.26 (PDF 28); §4.3, p.37 (PDF 39)

import Mathlib
import Definitions.Def_StreamColour_Params
import Definitions.Def_StreamColour_Reduction
import Definitions.Def_StreamColour_SampledPalette

namespace StreamColour

/-- Chakraborty, Chatterjee, Kundu, Mishra, *Streaming Graph Colouring Meets Molloy–Reed via Kernelization* (STOC 2027 submission, sha256 31a813b3…), Lemma 4.12, p.38 (PDF 40), with the objects of §4.2, p.26 and §4.3, p.37.

**Formalization Note.** The graph `H` and the lists come from `G`, `h = hParam C n k` and any proper `q`-colouring
`φK` of `G[K]` (`φK`'s values on `V(H)` are not used). The standing assumptions are those of §3 and of §4 (p.23): `∆ > 40h`,
with `h ≥ 2k + 2` from `C` large. The sample space has one priority and two arrays of length `p_max` per vertex of `G`, all
independent and uniform (the uniform law on the finite product), as in §4.3; the event reads `V(H)` only, so this is the
same probability as over `V(H)`. Repetitions are kept. `∃ C₀ Cp₀` is "for sufficiently large", before `n, ∆, k`. -/
theorem lemma_4_12 : ∃ C₀ Cp₀ : ℝ, ∀ C ≥ C₀, ∀ Cp ≥ Cp₀, ∀ (n Δ k : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (φK : Fin n → Fin (Δ - k)),
    1 ≤ k → k < Δ → Δ ≤ n - 1 → (∀ v, (G.neighborSet v).ncard ≤ Δ) → G.Colorable (Δ - k) →
    40 * hParam C n k < Δ →
    (∀ u v, u ∉ remainder G (hParam C n k) → v ∉ remainder G (hParam C n k) → G.Adj u v → φK u ≠ φK v) →
    (9 / 10 : ℝ) ≤ unifProb
      ((Fin n → Fin (gridSize n)) ×
        (Fin n → Fin (pMax Cp (Δ - k) n (hParam C n k)) → Fin (Δ - k)) ×
        (Fin n → Fin (pMax Cp (Δ - k) n (hParam C n k)) → Fin (Δ - k)))
      (fun ω => ∃ χ : Fin n → Fin (Δ - k),
        (∀ u ∈ remainder G (hParam C n k), ∀ v ∈ remainder G (hParam C n k), G.Adj u v → χ u ≠ χ v) ∧
        ∀ v ∈ remainder G (hParam C n k),
          χ v ∈ listL G (remainder G (hParam C n k)) φK v ∧
          χ v ∈ prefixColours (ω.2.1 v) (ω.2.2 v)
            (prefixA Cp (Δ - k) n (powerScale (liveDeg G (remainder G (hParam C n k)) v)))
            (prefixB Cp (Δ - k) n (hParam C n k)
              (powerScale (liveDeg G (remainder G (hParam C n k)) v)) (theta n (ω.1 v)))) := by sorry

end StreamColour
