-- Prove2me | Theorems.Thm_StreamColour_lemma_5_19
-- name    : StreamColour.lemma_5_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:53:06.299713+00:00
-- url     : https://prove2.me/theorems/34ad4e4e-abf3-423f-843f-1e94440ddf31
-- title:
--   Lemma 5.19 — reservoir completion from two independent short palettes
-- statement:
--   Let $H$ be a graph on at most $n$ vertices with maximum degree at most $\Delta$, let $q=\Delta-k$ with $1\le k<\Delta$, and let $L(v)\subseteq[q]$. Suppose there is $U\subseteq V(H)$ with
--
--   1. $|L(v)|\ge d_H(v)-k$ for every $v\in V(H)$;
--   2. $|L(u)|\ge d_H(u)+1$ for every $u\in U$;
--   3. $|N_H(v)\cap U|\ge\beta\Delta$ for every $v\in V(H)$.
--
--   Assume $\beta>0$ is fixed and $k\le\beta\Delta/2$. Put $t=\lceil C_{\mathrm{pal}}\ell^2\rceil\le q$ and independently sample two uniform $t$-element subsets $P_1(v),P_2(v)\subseteq[q]$ at each vertex. For sufficiently large $C_{\mathrm{pal}}$, depending only on $\beta$, with probability at least $1-n^{-10}$ there is a proper colouring $\psi$ of $H$ with $\psi(v)\in L(v)\cap(P_1(v)\cup P_2(v))$.
--
--   The set $U$ is used only to prove existence: the colouring does not refer to it.
--
--   Differences from the source:
--   - encoding: $|L(v)|\ge d_H(v)-k$ → $d_H(v)\le|L(v)|+k$; reason: natural-number subtraction would truncate
-- source:
--   Chakraborty, Chatterjee, Kundu, Mishra, Streaming Graph Colouring Meets Molloy–Reed via Kernelization (STOC 2027 submission, preprint, sha256 31a813b319e4af3fd96deb52ecd284fc2c478368ab1d9064bb951dcc884cc105), Lemma 5.19, p.72 (PDF 74)

import Mathlib
import Definitions.Def_StreamColour_Params
import Definitions.Def_StreamColour_GraphQuantities

namespace StreamColour

/-- Chakraborty, Chatterjee, Kundu, Mishra, *Streaming Graph Colouring Meets Molloy–Reed via Kernelization* (STOC 2027 submission, sha256 31a813b3…), Lemma 5.19, p.72 (PDF 74).

**Formalization Note.** `q = ∆ − k` with `1 ≤ k < ∆`, the standing assumption of §3, p.20. (i) is `d_H(v) ≤ |L(v)| + k`, so that nothing truncates.
`U` is a hypothesis only: `ψ` does not refer to it. `P₁, P₂` are independent uniform `t`-subsets at every vertex. `C₀` depends only on `β`. -/
theorem lemma_5_19 : ∀ β : ℝ, 0 < β → ∃ C₀ : ℝ, ∀ Cp ≥ C₀, ∀ (n Δ k : ℕ) (V : Type) [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (L : V → Finset (Fin (Δ - k))) (U : Finset V),
    Fintype.card V ≤ n → 1 ≤ k → k < Δ → (∀ v, dG H v ≤ Δ) →
    (∀ v, dG H v ≤ (L v).card + k) →
    (∀ u ∈ U, dG H u + 1 ≤ (L u).card) →
    (∀ v, β * (Δ : ℝ) ≤ (dIn H U v : ℝ)) →
    (k : ℝ) ≤ β * (Δ : ℝ) / 2 →
    sampleSize Cp n ≤ Δ - k →
    1 - 1 / (n : ℝ) ^ 10 ≤ unifProb
      ((V → TSubset (Δ - k) (sampleSize Cp n)) × (V → TSubset (Δ - k) (sampleSize Cp n)))
      (fun ω => ∃ ψ : V → Fin (Δ - k), (∀ u v, H.Adj u v → ψ u ≠ ψ v) ∧
        ∀ v, ψ v ∈ L v ∧ (ψ v ∈ (ω.1 v).1 ∨ ψ v ∈ (ω.2 v).1)) := by sorry

end StreamColour
