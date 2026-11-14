-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_tableau_machine_coupling
-- name    : QAlgorithms.DeWolf.tableau_machine_coupling
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:18:29.125237+00:00
-- url     : https://prove2.me/theorems/37042348-d140-4e8c-86bd-dfc2565ddb1a
-- title:
--   A tableau machine obeying the Clifford and Born update laws reproduces the circuit's output law
-- statement:
--   Let $F$ be a measurement-controlled Clifford circuit family, $x\in\{0,1\}^n$, and let $(\sigma, \mathrm{upd}, \mathrm{tab}, \mathrm{Inv}, s_0)$ be a classical state machine with $\mathrm{Inv}(s_0)$, $\Pi_{\mathrm{tab}(s_0)} = |x\rangle\langle x|$, whose update preserves $\mathrm{Inv}$, whose states satisfying $\mathrm{Inv}$ have valid tableaux, which conjugates the stabilizer projector by each gate, and which follows the Born rule on measurements (deterministic outcomes independent of the coin, random outcomes equal to the coin with probability $1/2$, post-measurement projector $P_\beta \Pi P_\beta / \mathrm{tr}(P_\beta \Pi)$). Run it for $\mathrm{steps}(n)$ controller rounds on $m \ge \mathrm{rbits}(n) + \mathrm{steps}(n)$ uniform bits (random bits $r$ = the first $\mathrm{rbits}(n)$ bits, one fresh coin per measurement). Then the invariant holds at the end and
--
--   $$\mathrm{Unif}(\{0,1\}^m).\mathrm{map}\big(\mathit{bits} \mapsto \Pi_{\mathrm{tab}(\mathrm{simLoop}(\mathit{bits}))}\big) = F.\mathrm{finalDist}(n,x).$$
--
--   Role: the probabilistic half of the Gottesman-Knill simulation: a stabilizer-state tracker driven by fair coins samples the circuit's final state with the right law.
-- source:
--   R. de Wolf, Quantum Computing: Lecture Notes, arXiv:1907.09415, Section 20.3, Theorem 6 and its proof, pp. 187-188; S. Aaronson and D. Gottesman, Improved simulation of stabilizer circuits, Phys. Rev. A 70 (2004) 052328, arXiv:quant-ph/0406196, Section III (the CHP tableau algorithm)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Stabilizer

namespace QAlgorithms.DeWolf

open QAlgorithms.Stabilizer QAlgorithms.Complexity

theorem tableau_machine_coupling (F : MCCFamily) (n : ℕ) (x : Qubits n) (σ : Type)
    (upd : CliffordOp n → σ → Bool → σ × Option Bool) (tab : σ → Tableau n) (Inv : σ → Prop) (s0 : σ)
    (h0 : Inv s0) (hx : tableauProjector (tab s0) = pureDensity (ket x))
    (hinv : ∀ op s b, Inv s → Inv (upd op s b).1)
    (hval : ∀ s, Inv s → IsValidTableau (tab s))
    (hgate : ∀ (op : CliffordOp n) s b, Inv s → (∀ M, op ≠ .measure M) →
      (upd op s b).2 = none ∧
      tableauProjector (tab (upd op s b).1) = op.mat * tableauProjector (tab s) * op.mat.conjTranspose)
    (hmeas : ∀ (M : Fin n → Pauli) s b, Inv s →
      ∃ β, (upd (.measure M) s b).2 = some β ∧
        (((((2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • PauliString.toMatrix ⟨0, M⟩) :
            Matrix (Qubits n) (Qubits n) ℂ) * tableauProjector (tab s)).trace = 1 ∧
            ∀ b', upd (.measure M) s b' = upd (.measure M) s b) ∨
          ((((2⁻¹ : ℂ) • (1 + (if true then -1 else 1) • PauliString.toMatrix ⟨0, M⟩) :
            Matrix (Qubits n) (Qubits n) ℂ) * tableauProjector (tab s)).trace = 2⁻¹ ∧ β = b)) ∧
        tableauProjector (tab (upd (.measure M) s b).1) =
          (((2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • PauliString.toMatrix ⟨0, M⟩) :
            Matrix (Qubits n) (Qubits n) ℂ) * tableauProjector (tab s)).trace⁻¹ • (((2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • PauliString.toMatrix ⟨0, M⟩) :
            Matrix (Qubits n) (Qubits n) ℂ) * tableauProjector (tab s) * ((2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • PauliString.toMatrix ⟨0, M⟩) :
            Matrix (Qubits n) (Qubits n) ℂ)))
    (m : ℕ) (hm : F.rbits.eval n + F.steps.eval n ≤ m) :
    let simLoop : List Bool → σ × List (Option Bool) × List Bool := fun bits =>
      (fun st : σ × List (Option Bool) × List Bool =>
        match F.ctrl n (bits.take (F.rbits.eval n)) st.2.1 with
        | none => st
        | some o => ((upd o st.1 (st.2.2.headD false)).1, st.2.1 ++ [(upd o st.1 (st.2.2.headD false)).2],
            match o with
            | .measure _ => st.2.2.tail
            | _ => st.2.2))^[F.steps.eval n] (s0, [], bits.drop (F.rbits.eval n))
    (∀ bits : List Bool, Inv (simLoop bits).1) ∧
      (PMF.uniformOfFintype (Fin m → Bool)).map
          (fun bits => tableauProjector (tab (simLoop (List.ofFn bits)).1)) =
        F.finalDist n x := by sorry

end QAlgorithms.DeWolf
