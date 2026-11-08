-- Prove2me | Theorems.Thm_QWildMatch_lemma_6_3
-- name    : QWildMatch.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T10:17:29.495204+00:00
-- url     : https://prove2.me/theorems/a8b02511-699b-47ee-8fc5-ba58e3ea95e1
-- title:
--   Lemma 6.3 — clean coherent defect-list interface with error $2\sqrt\eta$
-- statement:
--   There are absolute constants $C>0$ and $c$ such that for every alphabet, injective symbol encoding, $n$, $L\ge1$, $\ell$, $q$, references $B$ and $\eta\in(0,1)$ there is one query circuit $U_{\mathrm{list}}$ on block, list and scratch registers, with $Q$ text queries where, for $M=\max_b|J_b|$,
--
--   $$Q\le C\sqrt{M(q+1)}\,\bigl(1+\log(1/\eta)\bigr)\bigl(1+\log(M+2)\bigr)^c,$$
--
--   such that for every text $T$ and every unit vector of amplitudes $(\alpha_b)_b$ supported on blocks with at most $q$ defects,
--
--   $$\Bigl\|U_{\mathrm{list}}\sum_b\alpha_b|b,0,0\rangle-\sum_b\alpha_b|b,\mathrm{List}_b,0\rangle\Bigr\|\le2\sqrt\eta.$$
--
--   The bound for one promised block is the case of a single nonzero amplitude. This clean form is what allows the list to be recomputed inside amplitude amplification, with the block index in superposition.
--
--   **Formalization Note** The query register starts and ends at $(\mathtt{none},0)$; the list register's $0$ is $\emptyset$ and the scratch's $0$ is the all-false string.
--
--   Differences from the source:
--   - reading: query cost that of Lemma 6.2 and its inverse, up to constant factors → the shape of Lemma 6.2's bound at $M=\max_b|J_b|$ with its own absolute $C,c$; reason: one circuit serves every block, so the universe size is the maximum.
--   - reading: consecutive blocks of at most $L$ starts → the partition $bL\le s<(b+1)L$; reason: the page does not name a partition, and this is the canonical one.
--   - generalization: for every promised block, under the global Assumption 6.1 → the promise is needed only on blocks of nonzero amplitude; reason: the global promise is an instance.
--   - generalization: $\ell=m+r_+$ → any natural number $\ell$; reason: the page's $\ell$ is an instance and the lemma does not use its form.
--   - encoding: registers $|b,0,0\rangle$ → `Fin N_B × Finset _ × Qubits N`, with the query register at $(\mathtt{none},0)$; reason: this is one layout of the page's registers, and the query register is part of its scratch.
--   - encoding: $\mathrm{List}_b$ with sorted positions, count and padding → the `Finset` of pairs $(x,T[x])$; reason: these are encodings of the same set.
--   - encoding: the periodic function $B_b$ → an arbitrary function; reason: every function on the finite interval $J_b$ is periodic with period its length, and §6 uses no period.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…), Lemma 6.3, p.9

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QWildMatch_SparsePromise
import Definitions.Def_QWildMatch_IsCleanMark
import Definitions.Def_QWildMatch_textOracle

namespace QWildMatch

open QAlgorithms

set_option synthInstance.maxSize 256 in
/-- Lemma 6.3 (Clean coherent defect-list interface), Zhao et al., STOC 2027 submission (file sha256
9e87a9dd…), p.9.

**Formalization Note** The registers are block index, list, scratch (`Fin N_B × Finset _ × Qubits N`);
the list register's `∅` and the scratch's all-`false` are the `0`s of the page, and the query register
starts and ends at `(none, 0)`. The bound is on any superposition of blocks; "for every promised block
`b`" is the case of a single block. The promise is needed only on blocks with nonzero amplitude, which
is more general than Assumption 6.1's global promise. The cost is Lemma 6.2's shape at
`M = max_b |J_b|`, the universe size, maximized because one circuit serves every block. `ℓ` is an arbitrary
natural number here. -/
theorem lemma_6_3 :
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧
    ∀ (Sym : Type) [Fintype Sym] [DecidableEq Sym]
      (w : ℕ) (enc : Sym → (Fin w → ZMod 2)), Function.Injective enc →
    ∀ (n L l q : ℕ) (B : ℕ → Fin n → Sym) (η : ℝ), 1 ≤ L → 0 < η → η < 1 →
    ∃ (N Q : ℕ)
      (A : QueryAlg (Option (Fin n)) (Fin w → ZMod 2)
        (Fin (NB n L) × Finset (Fin n × Sym) × Qubits N) Q),
      (Q : ℝ) ≤ C *
          √(((Finset.univ.sup (fun b : Fin (NB n L) => (J n L l b).card) : ℕ) : ℝ) * ((q : ℝ) + 1)) *
          (1 + Real.log (1 / η)) *
          (1 + Real.log (((Finset.univ.sup (fun b : Fin (NB n L) => (J n L l b).card) : ℕ) : ℝ) + 2)) ^ c ∧
      ∀ (T : Fin n → Sym) (amp : Fin (NB n L) → ℂ), ∑ b, ‖amp b‖ ^ 2 = 1 →
        (∀ b, amp b ≠ 0 → (defects n L l B b T).card ≤ q) →
        ‖applyTo A (textOracle enc T)
            (∑ b, amp b • ket (((none, 0) : Option (Fin n) × (Fin w → ZMod 2)),
              ((b, ∅, fun _ => false) : Fin (NB n L) × Finset (Fin n × Sym) × Qubits N))) -
          ∑ b, amp b • ket (((none, 0) : Option (Fin n) × (Fin w → ZMod 2)),
              ((b, defectList n L l B b T, fun _ => false) :
                Fin (NB n L) × Finset (Fin n × Sym) × Qubits N))‖ ≤ 2 * √η := by sorry

end QWildMatch
