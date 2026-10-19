-- Prove2me | Theorems.Thm_StrategicRFx_Benefit_theorem_5
-- name    : StrategicRFx.Benefit.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:02.602107+00:00
-- url     : https://prove2.me/theorems/6d2d859e-3414-4134-9e4e-c1e16e14a450
-- title:
--   Theorem 5, p. 20 — with an RFx stage the buyer earns at least Π − π^F_1 − π^F_2, the most favorable bargaining profit
-- statement:
--   Let $\pi^F=(\pi^F_1,\pi^F_2)$ be the most favorable bargaining outcome, the solution of $\pi_i=\theta_i(\Pi-\pi_j-\Pi^{-i})^+$ for $\{i,j\}=\{1,2\}$. Let $\tilde\pi_1,\tilde\pi_2\ge 0$ be offers at which the buyer accepts both offers (her profit is then $\Pi-\tilde\pi_1-\tilde\pi_2$). Then
--   $$\Pi-\pi^F_1-\pi^F_2\ \le\ \Pi-\tilde\pi_1-\tilde\pi_2 ,$$
--   and moreover the buyer's profit $\Pi-\pi_1-\pi_2$ at every dual-sourcing equilibrium of simultaneous bargaining is at most $\Pi-\tilde\pi_1-\tilde\pi_2$.
--
--   The paper states: the buyer's equilibrium profit under sequential bargaining with an iterative tendering procedure is no less than her profit of the most favorable bargaining outcome $\pi^F$. The RFx stage thus gives the buyer a strategic benefit over bilateral bargaining without it.
--
--   **Formalization Note** The iterative tendering game is not formalized. Theorem 4 (p. 19) says that every iterative tendering procedure has a unique equilibrium outcome and that the buyer accepts both offers there; the statement therefore quantifies over **every** nonnegative offer pair at which the buyer accepts both offers, a class that contains the equilibrium outcome, exactly as the printed proof argues ("By Lemma 2 and Theorem 4 …"). "Accepts both offers" is defined from the Nash programs (8)–(12), not from Lemma 2's closed form; the class is nonempty (it contains $(0,0)$) and excludes large offers. Offers are nonnegative, as they are demanded profits. The second conjunct is the abstract's form of the comparison and uses Proposition 1.
-- source:
--   Chu, Rong & Zheng, The Strategic Benefit of Request for Proposal/Quotation, SSRN 3200030 (2019 preprint; Oper. Res. doi:10.1287/opre.2019.1964), Theorem 5, p. 20 (proof p. ec21)

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Setting

namespace StrategicRFx.Benefit

/-- Theorem 5 (p. 20). The buyer's equilibrium profit under sequential bargaining with an
iterative tendering procedure is no less than her profit `Π - π^F_1 - π^F_2` of the most favorable
bargaining outcome `π^F`. Stated for every nonnegative offer pair `(π̃_1, π̃_2)` at which the buyer
accepts both offers (her profit there is `Π - π̃_1 - π̃_2`); by Theorem 4 (not formalized) the
equilibrium outcome of any iterative tendering procedure is such a pair. The second conjunct
compares with every dual-sourcing equilibrium of simultaneous bargaining. -/
theorem theorem_5 (P : Params) (hP : Standing P) (πF : Fin 2 → ℝ)
    (hF : ∀ i, πF i = P.θ i * max (P.Pi - πF (other i) - P.PiEx i) 0)
    (t : Fin 2 → ℝ) (ht : ∀ i, 0 ≤ t i) (hacc : AcceptsBoth P t) :
    P.Pi - πF 0 - πF 1 ≤ P.Pi - t 0 - t 1 ∧
      ∀ π πex : Fin 2 → ℝ, IsSimuEquilibrium P π πex → P.Pi - π 0 - π 1 ≤ P.Pi - t 0 - t 1 := by sorry

end StrategicRFx.Benefit
