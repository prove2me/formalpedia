-- Prove2me | Theorems.Thm_SYKEdge_lemma_4_2
-- name    : SYKEdge.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:07:12.412871+00:00
-- url     : https://prove2.me/theorems/b117882d-3975-45e7-b9f6-5d43b5ad9cdf
-- title:
--   Lemma 4.2 — bosonic commutation relations $[b_i,b_j^*]=\delta_{ij}\mathrm{Id}$, $[b_i,N_j]=\delta_{ij}b_i$, $\{b_i,(-1)^{N_i}\}=0$
-- statement:
--   Let $b_i,b_i^*$ be the bosonic annihilation and creation operators on the Fock space $\mathcal F$ of $m$ modes, $N_j=b_j^*b_j$, and $(-1)^{N_i}f_r=(-1)^{r_i}f_r$. For all modes $i,j$,
--   $$[b_i,b_j]=[b_i^*,b_j^*]=0,\qquad [b_i,b_j^*]=\delta_{ij}\,\mathrm{Id},$$
--   $$[b_i,N_j]=\delta_{ij}\,b_i,\qquad [b_i^*,N_j]=-\delta_{ij}\,b_i^*,\qquad \{b_i,(-1)^{N_i}\}=\{b_i^*,(-1)^{N_i}\}=0,$$
--   where $[X,Y]=XY-YX$ and $\{X,Y\}=XY+YX$.
--
--   These are the canonical commutation relations that the twisted operators of Definition 4.3 deform.
--
--   **Formalization Note** Operators are linear maps of the finitely supported Fock space, multiplied by composition.
--
--   Differences from the source:
--   - reading: "For all i ≠ j ∈ Λ" printed before identities containing δ_ij → every identity for all i, j; reason: the proof checks both i = j ([b_i, b_i*] = Id) and i ≠ j; the δ_ij only has content with i = j allowed, and all identities hold there
--   - reading: a set Λ of modes → Λ = Fin m; reason: the paper uses Λ = ℋ, a finite ordered hyperedge list (p.21), and |r| = Σ_i r_i presumes finitely many modes
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Lemma 4.2, p.20

import Mathlib
import Definitions.Def_SYKEdge_Fock

namespace SYKEdge

/-- **Lemma 4.2** (Bosonic commutation relations), A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, p.20.

For all modes `i, j`: `[b_i, b_j] = [b_i*, b_j*] = 0`, `[b_i, b_j*] = δ_ij Id`,
`[b_i, N_j] = δ_ij b_i`, `[b_i*, N_j] = −δ_ij b_i*`, and `{b_i, (−1)^{N_i}} = {b_i*, (−1)^{N_i}} = 0`.

**Formalization Note.** The page prints "For all `i ≠ j ∈ Λ`" before identities containing `δ_ij`;
its proof checks the case `i = j` (`[b_i, b_i*] = Id`) and the case `i ≠ j`. The identities are stated
for all `i, j` (they hold at `i = j` too). Modes are `Fin m`; commutators are `XY − YX` and
anti-commutators `XY + YX` of linear maps of `F`, with products as composition. -/
theorem lemma_4_2 (m : ℕ) (i j : Fin m) :
    bop i ∘ₗ bop j - bop j ∘ₗ bop i = 0 ∧
    bdag i ∘ₗ bdag j - bdag j ∘ₗ bdag i = 0 ∧
    bop i ∘ₗ bdag j - bdag j ∘ₗ bop i = (if i = j then LinearMap.id else 0) ∧
    bop i ∘ₗ numOp j - numOp j ∘ₗ bop i = (if i = j then bop i else 0) ∧
    bdag i ∘ₗ numOp j - numOp j ∘ₗ bdag i = (if i = j then -bdag i else 0) ∧
    bop i ∘ₗ signPow (-1) i + signPow (-1) i ∘ₗ bop i = 0 ∧
    bdag i ∘ₗ signPow (-1) i + signPow (-1) i ∘ₗ bdag i = 0 := by sorry

end SYKEdge
