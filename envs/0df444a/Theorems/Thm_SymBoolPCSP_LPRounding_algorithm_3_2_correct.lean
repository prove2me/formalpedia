-- Prove2me | Theorems.Thm_SymBoolPCSP_LPRounding_algorithm_3_2_correct
-- name    : SymBoolPCSP.LPRounding.algorithm_3_2_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:30:36.51749+00:00
-- url     : https://prove2.me/theorems/29e5edea-4bbc-41ae-81a8-584ef0c20a7d
-- title:
--   §3.2 — the LP algorithm decides PCSP(Γ) when $\mathrm{Maj}_L$ or $\mathrm{AT}_L \in \mathrm{Pol}(\Gamma)$ for all odd $L$
-- statement:
--   Let $\Gamma = \{(P_R, Q_R) : R \in \tau\}$ be a finite family of Boolean promise relations, $P_R \subseteq Q_R$, and suppose that
--
--   1. $\mathrm{Maj}_L$ is a polymorphism of $\Gamma$ for every odd $L$, or
--   2. $\mathrm{AT}_L$ is a polymorphism of $\Gamma$ for every odd $L$.
--
--   Then the LP algorithm of §3.2 decides $\mathrm{PCSP}(\Gamma)$: for every instance $\Psi = (\Psi_P, \Psi_Q)$,
--   $$\Psi_P \text{ satisfiable} \;\Longrightarrow\; \text{the algorithm outputs ``satisfiable''} \;\Longrightarrow\; \Psi_Q \text{ satisfiable}.$$
--   Equivalently, it answers "satisfiable" on every YES instance and "unsatisfiable" on every NO instance. No symmetry of the relations is assumed.
--
--   This is the algebraic content of the Majority and Alternating-Threshold cases of Theorem 3.2: since the LP has size linear in the instance and LPs are solvable in polynomial time, it yields polynomial-time tractability of $\mathrm{PCSP}(\Gamma)$.
--
--   **Formalization Note** The algorithm's answer is `LPAlgAccepts 𝔸 X` (an LP feasibility test over $\mathbb Q$, see the definition file). The hypothesis is a disjunction of two universal statements, not "for every odd $L$, $\mathrm{Maj}_L$ or $\mathrm{AT}_L$". The polynomial running time, and hence the printed conclusion "PCSP(Γ) is polynomial-time tractable", is not formalized.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, pp. 13–15, §3.2 (algorithm and proof of correctness); algebraic core of the Maj_L and AT_L cases of Theorem 3.2, p. 15

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_LPRounding_Basic

open PCSPBLPAff.Symmetric

namespace SymBoolPCSP.LPRounding

/-- §3.2, pp. 13–15 (algebraic core of the Majority and Alternating-Threshold cases of
Theorem 3.2, p. 15): let `Γ` be a finite family of Boolean promise relations such that `Maj_L` is a
polymorphism of `Γ` for every odd `L`, or `AT_L` is a polymorphism of `Γ` for every odd `L`. Then
the LP algorithm of §3.2 decides `PCSP(Γ)`: it reports "satisfiable" on every instance with
`Ψ_P` satisfiable, and whenever it reports "satisfiable", `Ψ_Q` is satisfiable. -/
theorem algorithm_3_2_correct {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPQ : ∀ R, 𝔸.rel R ⊆ 𝔹.rel R)
    (hpol : (∀ L : ℕ, Odd L → IsPolymorphism 𝔸 𝔹 (SymBoolPCSP.CFixing.Maj L)) ∨
      (∀ L : ℕ, Odd L → IsPolymorphism 𝔸 𝔹 (SymBoolPCSP.CFixing.AT L))) :
    ∀ X : Instance τ ar,
      (SatIn X 𝔸 → LPAlgAccepts 𝔸 X) ∧ (LPAlgAccepts 𝔸 X → SatIn X 𝔹) := by sorry

end SymBoolPCSP.LPRounding
