-- Prove2me | Theorems.Thm_QuantumLTF_Example_lemma_5_5
-- name    : QuantumLTF.Example.lemma_5_5
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-15T20:37:56.107318+00:00
-- url     : https://prove2.me/theorems/e62279d0-cf0d-4962-bed7-699b57dcaa31
-- title:
--   Lemma 5.5 — disagreement under a one-coordinate perturbation
-- statement:
--   For the hard family of homogeneous halfspaces indexed by $z\in\{\pm1\}^m$, flipping one coordinate changes the target on Gaussian measure at most
--   $$d_{\gamma_n}(f_z,f_{z^{(i)}})\le\frac{4\pi\epsilon}{\sqrt m}.$$
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, STOC 2027 submission #347, Lemma 5.5, p. 76 (PDF p. 77).

import Mathlib
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Example_LowerModel

namespace QuantumLTF.Example

open QuantumLTF.Membership

theorem lemma_5_5 :
    ∀ m : ℕ, 1 ≤ m → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / (8 * Real.pi) →
      ∀ z : SignString m, ∀ i : Fin m,
        disagree (ltf (hardWeight m ε z) 0)
          (ltf (hardWeight m ε (Function.update z i (!(z i)))) 0) ≤
            4 * Real.pi * ε / Real.sqrt m := by sorry

end QuantumLTF.Example
