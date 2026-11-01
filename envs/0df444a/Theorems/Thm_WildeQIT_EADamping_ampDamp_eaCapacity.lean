-- Prove2me | Theorems.Thm_WildeQIT_EADamping_ampDamp_eaCapacity
-- name    : WildeQIT.EADamping.ampDamp_eaCapacity
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:39:58.367599+00:00
-- url     : https://prove2.me/theorems/7e1785ee-b49d-474c-8fae-a7dccd53b69a
-- title:
--   Proposition 21.6.2: $C_{EA}(\mathcal N_{AD})=I(\mathcal N_{AD})=\max_{p\in[0,1]}h_2(p)+h_2((1-\gamma)p)-h_2(\gamma p)$
-- statement:
--   Let $\mathcal N_{AD}$ be the amplitude damping channel with damping parameter $\gamma\in[0,1]$, with Kraus operators $A_0=|0\rangle\langle0|+\sqrt{1-\gamma}|1\rangle\langle1|$ and $A_1=\sqrt\gamma|0\rangle\langle1|$, and let $h_2(x)\equiv-x\log x-(1-x)\log(1-x)$ be the binary entropy function (base 2). The entanglement-assisted classical capacity of $\mathcal N_{AD}$ is equal to
--
--   $$
--   I(\mathcal N_{AD})=\max_{p\in[0,1]}\; h_2(p)+h_2((1-\gamma)p)-h_2(\gamma p).
--   $$
--
--   Precisely:
--
--   1. the channel mutual information $I(\mathcal N_{AD})$ equals the maximum over $p\in[0,1]$ of $h_2(p)+h_2((1-\gamma)p)-h_2(\gamma p)$, and the maximum is attained;
--   2. $I(\mathcal N_{AD})=\max_{\varphi_{AA'}}I(A;B)_\sigma$ with $\sigma_{AB}=\mathcal N_{AD}(\varphi_{AA'})$ is attained by some pure input $\varphi_{AA'}$;
--   3. $I(\mathcal N_{AD})$ is the supremum of all achievable rates of entanglement-assisted classical communication over $\mathcal N_{AD}$, that is, $C_{EA}(\mathcal N_{AD})=I(\mathcal N_{AD})$.
--
--   The optimal input is diagonal in the computational basis, with excited-state population $p$; the maximally entangled input of Corollary 21.2.1 ($p=1/2$) is in general not optimal.
--
--   **Formalization Note** Finite dimensions, logarithms base 2. $\mathcal N_{AD}$ is `ampDamp γ hγ`, $h_2$ the published `WildeQIT.binaryEntropy` ($0\log0=0$), $I(\cdot)$ is `channelMutualInfo`, and the capacity is the least upper bound (`IsLUB`) of the set of rates satisfying `IsAchievableEARate`, which avoids the junk value of a real `sSup`. Clause 3 is the capacity statement printed in the proposition; in the book it rests on Theorem 21.3.1.
--
--   Differences from the source:
--   - encoding: $C_{EA}(\mathcal N)$, "the supremum of all achievable rates" → `IsLUB {C | IsAchievableEARate N C}`; reason: a real `sSup` returns 0 on unbounded or empty sets, `IsLUB` states the supremum itself
--   - encoding: $\max_{\varphi_{AA'}}$ → `⨆` over pure inputs with reference `Fin m`, together with clause 2 asserting attainment; reason: every finite-dimensional reference is isometric to some $\mathbb C^m$, and clause 2 is the book's "max"
--   - reading: an $(n,C-\delta,\varepsilon)$ code, rate $\frac1n\log|\mathcal M|=C-\delta$ → at least $2^{n(C-\delta)}$ messages; reason: the book's rate is generally not of the form $\frac1n\log k$, and "at least" is the standard reading
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §21.6.2, Proposition 21.6.2, p. 610, (21.150)–(21.152); (21.156), p. 611; §21.1, p. 590

import Definitions.Def_WildeQIT_EADamping_ampDamp
import Definitions.Def_WildeQIT_EADamping_channelMutualInfo
import Definitions.Def_WildeQIT_EADamping_IsAchievableEARate
import Definitions.Def_WildeQIT_binaryEntropy

namespace WildeQIT.EADamping

open WildeQIT

/-- **Proposition 21.6.2 (entanglement-assisted classical capacity of the amplitude damping
channel).** Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8,
Proposition 21.6.2, (21.152), p. 610: the entanglement-assisted classical capacity of an amplitude
damping channel with damping parameter `γ ∈ [0, 1]` is equal to
`I(N_AD) = max_{p ∈ [0,1]} h₂(p) + h₂((1 − γ) p) − h₂(γ p)`, where
`h₂(x) ≡ −x log x − (1 − x) log(1 − x)` is the binary entropy function.

The three clauses:
1. the channel mutual information `I(N_AD)` is the maximum of `h₂(p) + h₂((1 − γ)p) − h₂(γp)` over
   `p ∈ [0, 1]` (the maximum is attained);
2. `I(N_AD)` is attained by a pure input `φ_{AA′}` (it is the book's `max_{φ_{AA′}} I(A; B)_σ`,
   (21.156));
3. `I(N_AD)` is the least upper bound of the achievable rates of entanglement-assisted classical
   communication over `N_AD`, i.e. `C_EA(N_AD) = I(N_AD)` (§21.1, p. 590).

**Formalization Note.** Finite dimensions, bits. `N_AD` is `ampDamp γ hγ` with the Kraus operators
(21.151); `h₂` is the published `WildeQIT.binaryEntropy` (base 2, `0 log 0 = 0`). The capacity,
"the supremum of all achievable rates", is stated through `IsLUB` on the set of achievable rates,
which avoids the junk value of a real `sSup`. -/
theorem ampDamp_eaCapacity (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    IsGreatest ((fun p : ℝ => binaryEntropy p + binaryEntropy ((1 - γ) * p) -
        binaryEntropy (γ * p)) '' Set.Icc 0 1) (channelMutualInfo (ampDamp γ hγ)) ∧
    IsGreatest (Set.range fun φ : WildeQIT.Degradable.PureInput (Fin 2) =>
        DattaDiscord.mutualInfo (idTensorApply (ampDamp γ hγ) (QAlgorithms.pureDensity φ.ψ)))
      (channelMutualInfo (ampDamp γ hγ)) ∧
    IsLUB {C : ℝ | IsAchievableEARate (ampDamp γ hγ) C} (channelMutualInfo (ampDamp γ hγ)) := by sorry

end WildeQIT.EADamping
