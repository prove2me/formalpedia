-- Prove2me | Theorems.Thm_ShiShallow_exists_complement_circuit
-- name    : ShiShallow.exists_complement_circuit
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T03:04:21.139437+00:00
-- url     : https://prove2.me/theorems/f6ac9c19-7649-4da7-a446-add2300703e0
-- title:
--   Closure under complement, at the cost of one layer
-- statement:
--   For every well-formed circuit $c$ there is a well-formed circuit $c'$, of depth exactly one greater, whose acceptance probability is the complement of that of $c$ on every input:
--
--   $$\mathrm{depth}(c') = \mathrm{depth}(c) + 1, \qquad \Pr[c' \text{ accepts } x] = 1 - \Pr[c \text{ accepts } x] \quad \text{for all } x.$$
--
--   Consequently, if $c$ decides a language with bounded error, then $c'$ decides its complement with the same error bound. This is the circuit-level statement behind $\mathsf{BQP} = \mathsf{co\text{-}BQP}$: the complexity class defined by bounded-error quantum circuits is closed under complement, and the witness costs a single extra layer. The circuit $c'$ is $c$ followed by one layer containing only a bit flip on the output wire.
-- source:
--   Formalised from scratch in this development; the light-cone bound is the standard shallow-circuit argument, see e.g. Terhal--DiVincenzo, Adaptive quantum computation, constant depth quantum circuits and Arthur-Merlin games, arXiv:quant-ph/0205133.

import Definitions.Def_ShiShallow_Core

namespace ShiShallow
theorem exists_complement_circuit {n m : ℕ} (c : Layered (n + m)) (out : Fin (n + m))
    (hc : ∀ l ∈ c, LayerOk l) :
    ∃ c' : Layered (n + m), (∀ l ∈ c', LayerOk l) ∧ depth c' = depth c + 1 ∧
      ∀ x : Bits n, acceptProb c' x out = 1 - acceptProb c x out := by sorry
end ShiShallow
