-- Prove2me | Theorems.Thm_PCNonBool_lemma_5_10
-- name    : PCNonBool.lemma_5_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:34:59.907207+00:00
-- url     : https://prove2.me/theorems/0caf9238-5776-4bd4-80e1-3a65f9624f4b
-- title:
--   Lemma 5.10 (corrected: split side measured without pigeon $i$) — $|\mathrm{PPHigh}_D(\mathrm{PigeonSplit}(\pi))| \le |\mathrm{PPHigh}_D(\pi)\setminus\mathrm{Touch}_{i,j,j',D}(\pi)|$
-- statement:
--   **Lemma 5.10.** Let $\mathbb F$ be a field of characteristic different from $2$, $G$ a bipartite graph, $U_a\subseteq U$, $V_a\subseteq V$, $i\in U_a$ and $j\ne j'\in N(i)\cap V_a$, and $D\in\mathbb R$. For every finite sequence $\pi$ of multilinear polynomials,
--   $$\bigl|\mathrm{PPHigh}_D^{\,U_a\setminus\{i\}}\bigl(\mathrm{PigeonSplit}_{i,j,j'}(\pi)\bigr)\bigr|\ \le\ \bigl|\mathrm{PPHigh}_D^{\,U_a}(\pi)\setminus\mathrm{Touch}_{i,j,j',D}(\pi)\bigr|,$$
--   where $\mathrm{PPHigh}^{\,W}_D$ denotes the set of monomial pairs of pairwise pigeon degree at least $D$ counted over the pigeons of $W$ (holes in $V_a$). In words: splitting on $(i,j,j')$ eliminates every high-degree pair touched by $(x_{i,j},x_{i,j'})$ and creates no new one, once the split pigeon is no longer counted.
--
--   This is the per-round progress measure of Algorithm 1 (Lemma 5.14).
--
--   Differences from the source:
--   - correction: |PPHigh_D(PigeonSplit_{i,j,j′}(π))| with ppdeg of the same graph G (Definition 5.5) → the split side is measured on the pigeons other than i: ppHighOn G (Ua.erase i) Va; reason: as printed the inequality fails: for a pigeon i with N(i) = {j, j′, h}, D = 1, P = {x_{i,j}x_{i,j′}x_{i,h} + 1, 1} and π = (x_{i,j}x_{i,j′}x_{i,h} + 1, 1), every pair of π has ppdeg 0 (x_{i,j}x_{i,j′}x_{i,h} ≡ −1), so the right side is 0, but the split line 1 − x_{i,h} has the pair (1, x_{i,h}) of ppdeg 1; Section 4's Q-degree after splitting is taken w.r.t. the split axioms, under which every variable of pigeon i is constant, and Algorithm 1 removes pigeon i (U′_ℓ = U_{ℓ−1} \ {i})
--   - generalization: π a polynomial calculus refutation of P → π any finite sequence of multilinear polynomials (redPM p = p for every line); reason: the proof uses only the decomposition p = x_{i,j}x_{i,j′}p₁ + x_{i,j}p₂ + x_{i,j′}p₃ + p₄ of each line; refutations in the reduced model have multilinear lines
--   - generalization: the fixed graph G → any induced instance G[Ua ⊔ Va] with i ∈ Ua and j ≠ j′ ∈ N(i) ∩ Va; reason: (Ua, Va) = (U, V) is the source's statement; Algorithm 1 applies the lemma to G_{ℓ−1}
--   - reading: ppdeg(m₀, m₁) = pdeg of the unique minimum-degree monomial in the class of m₀m₁ modulo ⟨PA ∪ {x² − 1}⟩ (Definition 5.5) → ppdegOn counts the pigeons i whose set H of holes occurring to an odd power in m₀m₁ is neither ∅ nor N(i); reason: the minimum-degree representative is not unique when |H| = |N(i)|/2, but whether pigeon i is mentioned is the same for every representative; when some pigeon has no hole the ideal is the unit ideal and the pigeon-by-pigeon count is still the Q-degree of Definition 4.9 (Proposition 5.6)
--   - reading: no field characteristic stated in the lemma; PigeonSplit (37) divides by 2 → ringChar F ≠ 2; reason: Section 5 works over fields of characteristic different from 2 (Theorem 5.1, p.26), which Definition 5.8's factor 1/2 presupposes
--   - encoding: PPHigh_D and Touch as sets of monomial pairs, unions over lines → Finset of unordered pairs (Sym2), set unions over the lines; reason: Definition 5.5's ⋃ is a set union of unordered pairs
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Lemma 5.10, (38), with the definition of touched, p.28 (PDF p.31)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_nbrOn
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_redPM
import Definitions.Def_PCNonBool_ppHighOn
import Definitions.Def_PCNonBool_touchSetOn
import Definitions.Def_PCNonBool_splitSeq

namespace PCNonBool

/-- **Lemma 5.10** (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), (38), p.28 (PDF p.31)), corrected. For every finite sequence `π` of
multilinear polynomials, every instance `G[Ua ⊔ Va]`, `i ∈ Ua` and `j ≠ j' ∈ N(i) ∩ Va`:
`|PPHigh_D(PigeonSplit_{i,j,j'}(π))| ≤ |PPHigh_D(π) \ Touch_{i,j,j',D}(π)|`, where the left side
is measured on the pigeons other than `i`.

**Formalization Note** With the left side measured in the same `G` (pigeon `i` included) the
printed inequality fails: for `N(i) = {j, j', h}`, `D = 1` and `π = (x_{i,j} x_{i,j'} x_{i,h} + 1, 1)`
every pair of `π` has `ppdeg 0`, while the split line `1 - x_{i,h}` has the pair `(1, x_{i,h})` of
`ppdeg 1` if `i` is counted. After the split,
every variable of pigeon `i` is constant modulo the split axioms (Section 4's Q-degree is taken
w.r.t. `PigeonSplit(P)`), and Algorithm 1 removes `i` (`U'_ℓ = U_{ℓ-1} \ {i}`). -/
theorem lemma_5_10 {F : Type*} [Field F] {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] (hF : ringChar F ≠ 2)
    (G : BipGraph U V) (Ua : Finset U) (Va : Finset V) (D : ℝ) (i : U) (j j' : V)
    (hi : i ∈ Ua) (hj : j ∈ nbrOn G Va i) (hj' : j' ∈ nbrOn G Va i) (hjj : j ≠ j')
    (π : List (MvPolynomial (Var G) F)) (hπ : ∀ p ∈ π, redPM p = p) :
    (ppHighOn G (Ua.erase i) Va D (splitSeq G i j j' π)).card ≤
      (ppHighOn G Ua Va D π \ touchSetOn G Ua Va D i j j' π).card := by sorry

end PCNonBool
