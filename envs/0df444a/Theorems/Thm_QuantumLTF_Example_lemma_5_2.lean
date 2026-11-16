-- Prove2me | Theorems.Thm_QuantumLTF_Example_lemma_5_2
-- name    : QuantumLTF.Example.lemma_5_2
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-15T20:41:46.797907+00:00
-- url     : https://prove2.me/theorems/30de5530-764b-4328-87fb-6ab8811df6ff
-- title:
--   Lemma 5.2 — discrete quantum Hermite transform
-- statement:
--   For $0<\eta<1/2$, $D>\log(1/\eta)$, and a power of two $M\ge C D^{9/4}\eta^{-13/4}$, there is a discrete quantum Hermite transform which uniformly maps every normalized superposition of degrees $0,\ldots,D-1$ to the corresponding superposition of discrete Hermite states with Euclidean error at most $\eta$. Its gate complexity is $O(\log^3 M\log(1/\eta))$.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, STOC 2027 submission #347, Lemma 5.2, pp. 58–59 (PDF pp. 59–60), citing JIS+26 Theorem 19.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Example_HermiteModel

namespace QuantumLTF.Example

open QAlgorithms QuantumLTF.Membership

theorem lemma_5_2 :
    ∃ Cg Csize : ℝ, 0 < Cg ∧ 0 < Csize ∧ ∀ D q : ℕ, 2 ≤ D →
      ∀ η : ℝ, 0 < η → η < 1 / 2 → Real.log (1 / η) < D →
      let M := 2 ^ q
      Cg * (D : ℝ) ^ (9 / 4 : ℝ) * η ^ (-13 / 4 : ℝ) ≤ M →
      ∃ c : Circuit gates12 q,
        (c.size : ℝ) ≤ Csize * (Real.log M) ^ 3 * Real.log (1 / η) ∧
        ∀ a : Fin D → ℂ, (∑ k, ‖a k‖ ^ 2) = 1 →
          ‖act c.unitary (∑ k, a k • degreeKet q k) -
            ∑ k, a k • discreteHermiteKet q k‖ ≤ η := by sorry

end QuantumLTF.Example
