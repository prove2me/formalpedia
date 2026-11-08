-- Prove2me | Theorems.Thm_StreamColour_lemma_5_4
-- name    : StreamColour.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:53:49.990093+00:00
-- url     : https://prove2.me/theorems/ae624097-2153-4d38-abb7-e3ec28445c9a
-- title:
--   Lemma 5.4 — expanded pieces: disjoint, $\Delta\pm O(h)$ vertices, $O(\Delta h)$ boundary edges, a gap in $d_X$
-- statement:
--   Let $\pi$ be an $(\eta,\varepsilon)$-almost-clique decomposition of a graph $G$ of maximum degree at most $\Delta$, with $\varepsilon<1/100$, and $\Delta>C_*h^2$ for a positive integer $h$ and sufficiently large $C_*$. Let $I$ index near pieces $C_i$, each with a maximal complement matching $M_i$ of fewer than $L=100h$ pairs; let $Q_i=C_i\setminus V(M_i)$ and $X_i=\{v:|N_G(v)\cap Q_i|\ge\frac{18}{25}\Delta\}$. Then:
--
--   1. the sets $X_i$ are pairwise disjoint, $C_i\subseteq X_i$, and $X_i\setminus C_i\subseteq S_0$;
--   2. $|X_i\setminus Q_i|=O(h)$ and $\Delta-O(h)\le|X_i|\le\Delta+O(h)$;
--   3. the number of edges with exactly one endpoint in $X_i$ is $\sum_{v\in X_i}e_{X_i}(v)=O(\Delta h)$;
--   4. $d_{X_i}(v)\ge\frac{18}{25}\Delta$ if $v\in X_i$, and $d_{X_i}(v)<\frac34\Delta$ if $v\notin X_i$.
--
--   The implicit constants and the threshold for $C_*$ depend only on the near constant $A$.
--
--   Differences from the source:
--   - generalization: $h=\lceil C(k+\ell^{10})\rceil$, promised $q$-colourable $G$, and $M_i$ from the procedure of Lemma 5.3 → any positive integer $h$, no colourability, and any maximal complement matching of fewer than $L$ pairs, for any index set of such pieces; reason: the proof uses only these properties; the paper's choices are special cases
--   - encoding: $O(\cdot)$, "sufficiently large $C_*$", and $L=\lceil100h\rceil$ → constants $c$ and $C_{*,0}$ that depend only on $A$, chosen before $h,n,\Delta,G$, and $L=100h$; reason: $h$ is an integer; the page says the implicit constants depend only on the fixed constants of the construction
-- source:
--   Chakraborty, Chatterjee, Kundu, Mishra, Streaming Graph Colouring Meets Molloy–Reed via Kernelization (STOC 2027 submission, preprint, sha256 31a813b319e4af3fd96deb52ecd284fc2c478368ab1d9064bb951dcc884cc105), Lemma 5.4, p.52 (PDF 54); (8), p.50; (9), p.51

import Mathlib
import Definitions.Def_StreamColour_ACD
import Definitions.Def_StreamColour_Expansion

namespace StreamColour

/-- Chakraborty, Chatterjee, Kundu, Mishra, *Streaming Graph Colouring Meets Molloy–Reed via Kernelization* (STOC 2027 submission, sha256 31a813b3…), Lemma 5.4, p.52 (PDF 54), with (8), p.50 and (9), p.51.

**Formalization Note.** `L = ⌈100h⌉ = 100h`. `I` indexes near pieces, each with a maximal complement matching `M i` of fewer than `L`
pairs; `Q_i` is `unmatched (piece π i) (M i)`, and `X_i` is `expanded G Δ Q_i`. `O(·)` is the constant `c`, which depends only on `A` and is
chosen before the graph, as is the threshold `Cs₀` for `C_∗` ("sufficiently large"). `h` is any positive integer, and no colourability
is assumed. In (i), `X_i \ C_i ⊆ S₀` is `π v = 0`. (iii) has both the count and the bound. -/
theorem lemma_5_4 : ∀ A : ℝ, 0 ≤ A → ∃ c Cs₀ : ℝ, ∀ Cs ≥ Cs₀, ∀ (h n Δ : ℕ) (G : SimpleGraph (Fin n))
    (π : Fin n → ℕ) (η ε : ℝ) (I : Finset ℕ) (M : ℕ → Finset (Fin n × Fin n)),
    1 ≤ h → 0 < η → 0 < ε → ε < 1 / 100 → (∀ v, (G.neighborSet v).ncard ≤ Δ) → IsACD η ε Δ G π →
    Cs * (h : ℝ) ^ 2 < (Δ : ℝ) →
    (∀ i ∈ I, 1 ≤ i ∧ IsNear A h Δ (piece π i) ∧ IsMaximalCM G (piece π i) (M i) ∧ (M i).card < 100 * h) →
    let Q := fun i => unmatched (piece π i) (M i)
    let X := fun i => expanded G Δ (Q i)
    (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (X i) (X j)) ∧
    ∀ i ∈ I,
      piece π i ⊆ X i ∧ (∀ v ∈ X i, v ∉ piece π i → π v = 0) ∧
      (((X i \ Q i).card : ℝ) ≤ c * h) ∧
      ((Δ : ℝ) - c * h ≤ ((X i).card : ℝ) ∧ ((X i).card : ℝ) ≤ (Δ : ℝ) + c * h) ∧
      edgesLeaving G (X i) = ∑ v ∈ X i, extDeg G (X i) v ∧
      ((∑ v ∈ X i, extDeg G (X i) v : ℕ) : ℝ) ≤ c * (Δ : ℝ) * h ∧
      (∀ v ∈ X i, (18 / 25 : ℝ) * (Δ : ℝ) ≤ (dIn G (X i) v : ℝ)) ∧
      (∀ v, v ∉ X i → (dIn G (X i) v : ℝ) < (3 / 4 : ℝ) * (Δ : ℝ)) := by sorry

end StreamColour
