-- Prove2me | Theorems.Thm_TopDownParity1043_Main_circuit_to_protocol
-- name    : TopDownParity1043.Main.circuit_to_protocol
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T15:49:40.606196+00:00
-- url     : https://prove2.me/theorems/5cd8bdae-6c61-406d-a155-c97a385f737d
-- title:
--   Lemma 1 — circuit-to-protocol direction
-- statement:
--   Let $f$ be a Boolean function on $n$ coordinates, and let $d,m$ be natural numbers. If a De Morgan circuit computes $f$, has depth at most $d$, and every gate has at most $2^m$ inputs, then
--
--   $$
--   \operatorname{HasKWProtocol}(f,d,m).
--   $$
--
--   This is the circuit-to-protocol direction of Lemma 1. The protocol has at most $d$ messages and at most $2^m$ possible messages at every internal node. Constants, literal outputs, empty gates, and the cases $n=0$, $d=0$, or $m=0$ are included. This implication transfers communication lower bounds to circuit lower bounds in Theorem 3.
-- source:
--   Oliver Korten, Top-Down Lower Bounds for All Depths, STOC 2027 submission #1043, Lemma 1, p.2, circuit-to-protocol implication; canonical manuscript https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1043.pdf

import Mathlib
import Definitions.Def_TopDownParity1043_Main_KW
set_option autoImplicit false

theorem TopDownParity1043.Main.circuit_to_protocol (n d m : ℕ) (f : ParityBarrier563.Trilinear.BoolFn (Fin n)) :
    (∃ C : ParityBarrier563.Trilinear.Circuit (Fin n),
      C.depth ≤ d ∧ TopDownParity1043.Main.maxFanIn C ≤ 2 ^ m ∧ C.Computes f) →
      TopDownParity1043.Main.HasKWProtocol f d m := by sorry
