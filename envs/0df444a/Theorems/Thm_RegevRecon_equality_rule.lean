-- Prove2me | Theorems.Thm_RegevRecon_equality_rule
-- name    : RegevRecon.equality_rule
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:05:12.399756+00:00
-- url     : https://prove2.me/theorems/3b7c1f1a-33f1-4738-8afb-2c49c1008092
-- title:
--   (29)–(30) — the equality rule
-- statement:
--   For probability vectors $\mu,\nu$ on $\mathbb F_p$ there is a unitary $V_{\mathrm{eq}}(\mu,\nu)$ on two qudits, depending only on $\mu$ and $\nu$, such that for every $a$ and every $d$
--
--   $$
--   V_{\mathrm{eq}}|g_a\rangle=\sqrt{(\mu*\nu)_a}\,|a\rangle\otimes|0\rangle,\qquad V_{\mathrm{eq}}\bigl(|\phi_d(\mu)\rangle\otimes|\phi_d(\nu)\rangle\bigr)=|\phi_d(\mu*\nu)\rangle\otimes|0\rangle.
--   $$
--
--   So two messages about one symbol compress into one qudit with no knowledge of $d$, and the classical update is the convolution.
--
--   Differences from the source: none.
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), (29)–(30), p.10

import Mathlib
import Definitions.Def_RegevRecon_BPQMUnitaries

namespace RegevRecon

/-- **The equality rule (29)–(30)**. Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), p.10: for probability vectors `μ, ν` there is a unitary `V_eq(μ, ν)`,
depending only on `μ` and `ν`, with `V_eq |g_a⟩ = √((μ ∗ ν)_a) |a⟩ ⊗ |0⟩`, and hence, for **every** `d`,
`V_eq (|ϕ_d(μ)⟩ ⊗ |ϕ_d(ν)⟩) = |ϕ_d(μ ∗ ν)⟩ ⊗ |0⟩`. -/
theorem equality_rule {p : ℕ} [Fact p.Prime] (μ ν : Vec p) (hμ : IsProbVec μ) (hν : IsProbVec ν) :
    ∃ V ∈ Matrix.unitaryGroup (ZMod p × ZMod p) ℂ,
      (∀ a : ZMod p, qditAct V (gVector μ ν a) =
        WithLp.toLp 2 fun x => if x = (a, 0) then ((Real.sqrt (conv μ ν a) : ℝ) : ℂ) else 0) ∧
      ∀ d : ZMod p, qditAct V (qditTensor (messageState μ d) (messageState ν d)) =
        withZero (messageState (conv μ ν) d) := by sorry

end RegevRecon
