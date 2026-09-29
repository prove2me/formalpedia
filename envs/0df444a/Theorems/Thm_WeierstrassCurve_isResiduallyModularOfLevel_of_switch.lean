-- Prove2me | Theorems.Thm_WeierstrassCurve_isResiduallyModularOfLevel_of_switch
-- name    : WeierstrassCurve.isResiduallyModularOfLevel_of_switch
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/6c362136-824c-5779-b6b4-f24772c6e13f
-- title:
--   Mod-5 transport of residual modularity across the 3–5 switch
-- statement:
--   Let $W$ and $W'$ be Weierstrass curves over $\mathbb{Z}$ and let $N$ be a natural number. Three hypotheses are assumed. First, `hmod`: $W'$ is modular of level $N$ in the project's sense `IsModularModelOfLevel`, i.e. there is a cusp form $f$ of weight $2$ on $\Gamma_0(N)$ which is a normalised eigenform and whose $q$-expansion coefficient at every prime $p$ with $p \nmid \Delta(W')$ and $p \nmid N$ equals $a_p(W')$, where $a_p(W') := \mathrm{tr}\,\mathrm{Frob}_p$ of the reduction of $W'$ modulo $p$ (`apOfModel`), and "good prime for a model" means exactly $p \nmid \Delta$ (`IsGoodPrimeFor`). Second, `hND`: every prime $\ell$ dividing $\Delta(W')$ divides $N$. Third, `hcong`: for every prime $\ell \ne 5$ with $\ell \nmid \Delta(W)$ and $\ell \nmid \Delta(W')$ one has $5 \mid a_\ell(W') - a_\ell(W)$ in $\mathbb{Z}$. The conclusion is `W.IsResiduallyModularOfLevel 5 N`: there exist a normalised weight-$2$ eigenform $f$ on $\Gamma_0(N)$ and a maximal ideal $\mathfrak{m}$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ with $5 \in \mathfrak{m}$, such that for every prime $\ell$ with $\ell \nmid \Delta(W)$, $\ell \nmid N$ and $\ell \ne 5$ there is an algebraic integer $a$ with $a = \mathrm{qCoeff}\,f\,\ell$ in $\mathbb{C}$ and $a - a_\ell(W) \in \mathfrak{m}$. No hypothesis of nonvanishing discriminant, semistability or irreducibility of a mod-$p$ representation is imposed on either curve: the statement is purely the transport of a congruence of traces into a residual-modularity witness, and it keeps the level $N$ of $W'$ unchanged.
--
--   This is the final bookkeeping step of the $3$–$5$ switch in Wiles's proof of modularity for semistable curves, as in the proof of Theorem 3.48 of Darmon–Diamond–Taylor: once the auxiliary curve $W'$ produced by the switch is known to be modular, the congruence $a_\ell(W') \equiv a_\ell(W) \pmod 5$ at common good primes makes $W$ residually modular at $5$. Compared with the textbook formulation, "residually modular mod $5$" is here realised concretely by a maximal ideal of $\overline{\mathbb{Z}} =$ the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ containing $5$, rather than by a prime of a Hecke eigenvalue field or a residual Galois representation, and the hypothesis that the bad primes of $W'$ divide $N$ is what converts goodness for $W$ away from $N$ into goodness for $W'$. It feeds into [`WeierstrassCurve.modularity_of_semistableModel`](thm.html#WeierstrassCurve.modularity_of_semistableModel), where the mod-$5$ residual modularity obtained here is the input to modularity lifting at $5$, and hence into [`FreyPackage.modularRepOfConductorLevel`](thm.html#FreyPackage.modularRepOfConductorLevel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_isResiduallyModularOfLevel_of_switch.lean

import Definitions.Def_WeierstrassCurve_ModularityProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.isResiduallyModularOfLevel_of_switch {W W' : WeierstrassCurve ℤ} {N : ℕ}
    (hmod : W'.IsModularModelOfLevel N)
    (hND : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ W'.Δ → ℓ ∣ N)
    (hcong : ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → W'.IsGoodPrimeFor ℓ → ℓ ≠ 5 →
      (5 : ℤ) ∣ (W'.apOfModel ℓ - W.apOfModel ℓ)) :
    W.IsResiduallyModularOfLevel 5 N := by sorry
