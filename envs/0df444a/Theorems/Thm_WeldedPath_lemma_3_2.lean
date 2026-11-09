-- Prove2me | Theorems.Thm_WeldedPath_lemma_3_2
-- name    : WeldedPath.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:04:49.706653+00:00
-- url     : https://prove2.me/theorems/9073fc47-211e-4a54-931c-7432122c2d21
-- title:
--   Lemma 3.2 — edge-color counts per column
-- statement:
--   Let $G_n$ be a valid welded trees instance. Let $\alpha_1$ be the color not used by the two edges at the entrance $r(T_1)$. For every color $\alpha'$ and every column $c\in[1,n]$, the number $\gamma(\alpha',c)$ of edges of color $\alpha'$ between columns $c-1$ and $c$ of $T_1$ is
--   $$
--   \gamma(\alpha',c)=\begin{cases}\left\lfloor \dfrac{2^c}{3}\right\rfloor & \text{if } c \text{ is odd and } \alpha'=\alpha_1, \text{ or } c \text{ is even and } \alpha'\neq\alpha_1,\\[2mm] \left\lceil \dfrac{2^c}{3}\right\rceil & \text{otherwise.}\end{cases}
--   $$
--   For $T_2$ the same holds for edge-columns $c\in[n+2,2n+1]$ with $c$ replaced by $2n-c+2$, where $\alpha_1$ is now the color not used by the edges at the exit $r(T_2)$.
--
--   So every color class of a column holds a third of its edges up to rounding, which bounds the sizes of the permuted edge classes from below.
--
--   Differences from the source:
--   - generalization: standing assumption of §3.1: n even → every n; reason: the counts do not depend on the parity of n; the even case is a special case
--   - encoding: α₁, the color not used by the edges at the root → every α₁ different from the colors of the two root edges; reason: under a proper coloring the two root edges have different colors, so this α₁ is unique
--   - encoding: edges in column c of T₂, c ∈ [n+2, 2n+1] → tree edges of T₂ whose child lies in column c − 1; reason: p.15: the edges in column c are those between columns c − 1 and c
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), Lemma 3.2, p.15

import Mathlib
import Definitions.Def_WeldedPath_gammaCount

namespace WeldedPath

open WeldedInstance

/-- **Lemma 3.2** (Lemma 55 in the full version of [CCG23]; Carolan, Childs, Coudron, Gilani,
Miloschewsky, Podder, arXiv:2611.05912 (sha256 b31400a0…), Lemma 3.2, p.15). Let `α_1` be the
color that is not used by any edges to `r(T_1)`. For any color `α′ ∈ C`, let `γ(α′, c)` denote the
number of edges colored `α′` in column `c ∈ [n]` of `T_1`. Then
`γ(α′, c) = ⌊2^c/3⌋` if `c` is odd and `α′ = α_1` or `c` is even and `α′ ≠ α_1`, and `⌈2^c/3⌉`
otherwise (19). For `T_2` (i.e. `c ∈ [n + 2, 2n + 1]`), replace `c` in (19) with `2n − c + 2` and let
`α_1` be the color not used by the edges incident to `r(T_2)`.

**Formalization Note.** The edges in column `c` are those between columns `c − 1` and `c` (p.15).
In `T_1` (indices below `2^{n+1} − 1`) these are the tree edges whose child lies in column `c`; in
`T_2` (edge-columns `c ∈ [n + 2, 2n + 1]`) the tree edges whose child lies in column `c − 1`. The
edges to `r(T_1)` are `{1, 0}` and `{2, 0}`; those incident to `r(T_2)` are `{2^{n+1}, 2^{n+1} − 1}`
and `{2^{n+1} + 1, 2^{n+1} − 1}`. -/
theorem lemma_3_2 (n : ℕ) (G : WeldedInstance n) (hG : G.IsValid) :
    (∀ α₁ : Fin 3, α₁ ≠ G.color (.tree 1) → α₁ ≠ G.color (.tree 2) →
      ∀ α' : Fin 3, ∀ c : ℕ, 1 ≤ c → c ≤ n →
        (gammaCount G true α' c : ℝ) =
          if (Odd c ∧ α' = α₁) ∨ (Even c ∧ α' ≠ α₁) then (⌊(2 : ℝ) ^ c / 3⌋₊ : ℝ)
          else (⌈(2 : ℝ) ^ c / 3⌉₊ : ℝ)) ∧
    (∀ α₁ : Fin 3, α₁ ≠ G.color (.tree (2 ^ (n + 1))) → α₁ ≠ G.color (.tree (2 ^ (n + 1) + 1)) →
      ∀ α' : Fin 3, ∀ c : ℕ, n + 2 ≤ c → c ≤ 2 * n + 1 →
        (gammaCount G false α' (c - 1) : ℝ) =
          if (Odd (2 * n - c + 2) ∧ α' = α₁) ∨ (Even (2 * n - c + 2) ∧ α' ≠ α₁) then
            (⌊(2 : ℝ) ^ (2 * n - c + 2) / 3⌋₊ : ℝ)
          else (⌈(2 : ℝ) ^ (2 * n - c + 2) / 3⌉₊ : ℝ)) := by sorry

end WeldedPath
