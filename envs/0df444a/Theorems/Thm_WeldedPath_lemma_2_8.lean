-- Prove2me | Theorems.Thm_WeldedPath_lemma_2_8
-- name    : WeldedPath.lemma_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:15:07.22148+00:00
-- url     : https://prove2.me/theorems/afefe916-bac6-4c45-9b53-3fc6b26275f1
-- title:
--   Lemma 2.8 — the exact compressed permutation query
-- statement:
--   Let $s\ge 3$, let the answer register be $\{0,1\}^d$ with $s\le 2^d$, and let $\widehat{\mathrm{cpO}}_x$ be the exact compressed query, $\mathrm{cpO}_x$ the ordinary compressed query, $O_x$ the standard query and $\mathcal I_s$ the intertwiner. There is an absolute constant $C$ such that, for coherently controlled queries $\sum_c|c\rangle\langle c|\otimes\widehat{\mathrm{cpO}}_{x_c}$ with any finite control register, any queried values $x_c$ and any directions (forward or inverse):
--
--   1. $\widehat{\mathrm{cpO}}$ is self-adjoint and $\|\widehat{\mathrm{cpO}}\|\le 1$;
--   2. $\widehat{\mathrm{cpO}}\,\mathcal I_s=\mathcal I_s\,O$;
--   3. $\widehat{\mathrm{cpO}}$ changes the database size by at most $1$: $\langle c',y',J|\widehat{\mathrm{cpO}}|c,y,I\rangle=0$ whenever $\big||J|-|I|\big|>1$;
--   4. if $4(t+4)\le s$, then
--   $$
--   \big\|(\widehat{\mathrm{cpO}}-\mathrm{cpO})\,\Pi_{\le t,\mathrm I}\big\|\ \le\ \frac{C}{\sqrt s}.
--   $$
--
--   The exact query reproduces the random-permutation oracle exactly after compression and differs from the ordinary compressed query by $O(s^{-1/2})$ on databases with few records; this removes the $O(t/s)$ term of earlier compressed-oracle bounds.
--
--   Differences from the source:
--   - generalization: a single query ĉpO_x, the same for inverse queries and under coherent control → coherently controlled queries Σ_c |c⟩⟨c| ⊗ ĉpO with any finite control register and any per-control queried value and direction; reason: a one-element control register gives the single forward or inverse query
--   - reading: changes the database size by at most 1 → matrix entries between basis states whose database sizes differ by more than 1 vanish; reason: this is what the phrase means for an operator on the database basis
--   - reading: O(1/√s) → C/√s with one absolute constant C chosen before s, d, the control data and t; reason: the bound is uniform in all parameters
--   - encoding: [s], answer register {0,1}^d → Fin s (0-based), Qubits d with s ≤ 2^d, values written in binary; reason: a relabelling and an injective encoding
--   - encoding: G_{s,r}^{-1/2} on level r → functional calculus of x ↦ (√x)^{-1}, equal to 0 at 0; reason: G_{s,r} vanishes off level r and is invertible on it, so this is the same operator extended by 0
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), Lemma 2.8, p.13

import Mathlib
import Definitions.Def_WeldedPath_exactCpO

namespace WeldedPath

open InjDb

/-- **Lemma 2.8** (Exact compressed oracle query; Carolan, Childs, Coudron, Gilani, Miloschewsky,
Podder, arXiv:2611.05912 (sha256 b31400a0…), Lemma 2.8, p.13). The operator `ĉpO_x` is a
self-adjoint contraction that satisfies `ĉpO_x I_s = I_s O_x` and changes the database size by at
most 1. Furthermore, if `4(t + 4) ≤ s`, then `‖(ĉpO_x − cpO_x) Π_{≤t,I}‖ = O(1/√s)` (15). The same
holds for inverse queries and under coherent control.

**Formalization Note.**
1. The statement is made for coherently controlled queries `Σ_c |c⟩⟨c| ⊗ ĉpO_{x_c}` with any
   finite control register and any assignment `c ↦ (x_c, inv_c)` of a queried value and a
   direction (`inv_c = true` for an inverse query); a single forward or inverse query is the case
   of a one-element control register.
2. `s ≥ 3` is the standing assumption of §2 (p.8). The answer register is `{0,1}^d` with
   `s ≤ 2^d` (`encode`).
3. `O(1/√s)` is one absolute constant `C`, chosen before `s`, `d`, the control data and `t`.
4. "Changes the database size by at most 1": the matrix entry between basis states whose database
   sizes differ by more than one vanishes. -/
theorem lemma_2_8 :
    ∃ C : ℝ, 0 < C ∧
      ∀ s d : ℕ, 3 ≤ s → s ≤ 2 ^ d →
      ∀ (Ctl : Type) [Fintype Ctl] [DecidableEq Ctl] (ctl : Ctl → Fin s × Bool),
      let E : Hil (Ctl × (QAlgorithms.Qubits d × InjDb s)) →L[ℂ]
          Hil (Ctl × (QAlgorithms.Qubits d × InjDb s)) :=
        controlled fun c => exactCpO d (ctl c).1 (ctl c).2
      let O : Hil (Ctl × (QAlgorithms.Qubits d × InjDb s)) →L[ℂ]
          Hil (Ctl × (QAlgorithms.Qubits d × InjDb s)) :=
        controlled fun c => cpO d (ctl c).1 (ctl c).2
      let Std : Hil (Ctl × (QAlgorithms.Qubits d × Equiv.Perm (Fin s))) →L[ℂ]
          Hil (Ctl × (QAlgorithms.Qubits d × Equiv.Perm (Fin s))) :=
        controlled fun c => stdQuery d (ctl c).1 (ctl c).2
      let Is : Hil (Ctl × (QAlgorithms.Qubits d × Equiv.Perm (Fin s))) →L[ℂ]
          Hil (Ctl × (QAlgorithms.Qubits d × InjDb s)) :=
        opTensor 1 (opTensor 1 (intertwiner s))
      IsSelfAdjoint E ∧ ‖E‖ ≤ 1 ∧ E.comp Is = Is.comp Std ∧
      (∀ (c c' : Ctl) (y y' : QAlgorithms.Qubits d) (I J : InjDb s),
        (I.size + 1 < J.size ∨ J.size + 1 < I.size) →
          inner ℂ (ket (c', (y', J))) (E (ket (c, (y, I)))) = 0) ∧
      ∀ t : ℕ, 4 * (t + 4) ≤ s →
        ‖(E - O).comp (diagProj fun p : Ctl × (QAlgorithms.Qubits d × InjDb s) =>
            p.2.2.size ≤ t)‖ ≤ C / Real.sqrt s := by sorry

end WeldedPath
