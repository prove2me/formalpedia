-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_implicitMeasurement
-- name    : QAlgorithms.Nannicini.implicitMeasurement
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:51:39.38198+00:00
-- url     : https://prove2.me/theorems/3421f0b6-6aec-44d7-b14e-6f791529f97e
-- title:
--   Principle of implicit measurement
-- statement:
--   This is the principle of implicit measurement, in the form of the consistency claim the text makes right after the proposition.
--
--   Let $|\psi\rangle$ be a $q$-qubit state (a unit vector in $(\mathbb C^2)^{\otimes q}$). For a list $L=(k_1,\dots,k_s)$ of distinct qubits and a string $y\in\{0,1\}^q$, let $\Pr_\psi[L\to y]$ be the probability that measuring the qubits $k_1,\dots,k_s$ one at a time in the computational basis (Postulate 3, with the state collapsing after each measurement) gives outcome $y_{k_i}$ on qubit $k_i$ for every $i$. Let $l$ and $r$ be lists of qubits such that $l$ followed by $r$ has no repeated qubit. Then for every $y\in\{0,1\}^q$,
--
--   $$
--   \Pr_\psi[l\to y]=\sum_{\substack{z\in\{0,1\}^q\\ z_i=y_i\ \forall i\notin r}}\Pr_\psi[l\,r\to z].
--   $$
--
--   In words, the outcome distribution on the qubits $l$ does not change if the qubits $r$, which are never measured, are also measured afterwards and their outcomes are discarded.
--
--   This is what lets you treat discarded working registers as measured. It is the basis for the uncomputation discussion and for reduced density matrices.
--
--   **Formalization Note** The sum runs over all strings that agree with $y$ outside $r$. The coordinates outside $l$ and $r$ do not affect either side, so fixing them to $y$ only avoids counting the same term more than once.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 32, Proposition 1.50. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Measurement
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms

open scoped ComplexOrder

/-- Nannicini p.32, Proposition 1.50 (principle of implicit measurement), in the form of the
consistency claim argued right after it: measuring the qubits `l` one at a time (Post. 3,
Prop. 1.27) gives outcome `y` on `l` with the same probability as measuring the qubits `l`
and then further, never-measured qubits `r`, and discarding the outcomes on `r` (summing over
them). The state `ψ` is a unit vector. -/
theorem implicitMeasurement {q : ℕ} (ψ : EuclideanSpace ℂ (Qubits q)) (hψ : IsState ψ)
    (l r : List (Fin q)) (hlr : (l ++ r).Nodup) (y : Qubits q) :
    seqMeasProb ψ l y =
      ∑ z ∈ Finset.univ.filter (fun z : Qubits q => ∀ i, i ∉ r → z i = y i),
        seqMeasProb ψ (l ++ r) z := by sorry




end QAlgorithms.Nannicini
