-- Prove2me | Theorems.Thm_SwitchbackExp_Design_lemma_EC_2
-- name    : SwitchbackExp.Design.lemma_EC_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:35.060617+00:00
-- url     : https://prove2.me/theorems/55db69b9-3476-4cf8-bbe7-bcbb231dc138
-- title:
--   Lemma EC.2, p. ec2 — for q_i ∈ (0,1), 1/∏q_i + 1/∏(1−q_i) ≥ 2^{n+1}, with equality iff every q_i = 1/2
-- statement:
--   For every $n$ and all $q_1,\dots,q_n\in(0,1)$, the function
--   $$f(q_1,\dots,q_n)=\frac1{\prod_{i=1}^n q_i}+\frac1{\prod_{i=1}^n(1-q_i)}$$
--   satisfies
--   $$f(q_1,\dots,q_n)\ge 2^{n+1},$$
--   and equality holds if and only if $q_1=\dots=q_n=1/2$.
--
--   This inequality is what makes fair coins optimal in Theorem 1: at the extreme outcomes every term of the risk has the form $f(\cdot)\,B^2$.
--
--   **Formalization Note** The page's $n\in\mathbb N$ means $n\ge1$ (p. ec1). The statement also holds at $n=0$ (both sides equal $2$, and the equality condition is vacuous), so the restriction is dropped; this is a strengthening.
-- source:
--   Bojinov, Simchi-Levi, Zhao, Design and Analysis of Switchback Experiments, arXiv:2009.00148v4 (Management Science 69(7), 2023), Lemma EC.2, p. ec2

import Mathlib
import Definitions.Def_SwitchbackExp_Design_Model
import Definitions.Def_SwitchbackExp_Design_Setting

namespace SwitchbackExp.Design

/-- Lemma EC.2 (p. ec2): for `q₁, …, q_n ∈ (0,1)`, `1/∏ q_i + 1/∏ (1 − q_i) ≥ 2^{n+1}`, with equality
iff every `q_i = 1/2`. -/
theorem lemma_EC_2 (n : ℕ) (q : Fin n → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1) :
    2 ^ (n + 1) ≤ 1 / ∏ i, q i + 1 / ∏ i, (1 - q i) ∧
    (1 / ∏ i, q i + 1 / ∏ i, (1 - q i) = 2 ^ (n + 1) ↔ ∀ i, q i = 1 / 2) := by sorry

end SwitchbackExp.Design
