-- Prove2me | Theorems.Thm_StretchDepth_prob_mem_Q
-- name    : StretchDepth.prob_mem_Q
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:08:05.930163+00:00
-- url     : https://prove2.me/theorems/cfe2261f-a8a6-4eb7-82f8-cb5a001c824b
-- title:
--   Proof of Theorem 1 — $\Pr[w\in Q]\le e^{-s/8}+O(q^2/s)$
-- statement:
--   Let $f$ be a family of deterministic procedures (one per challenge) with at most $q_R$ queries on every real pair, and $H$ a query procedure with at most $q_H$ queries on every oracle. Let $0<p\le1$ and $s=p2^n$. Then $|Q|\le q_R(1+q_H)$ for all $G,S^+,z$, and in the correlated experiment,
--   $$
--   \Pr[w\in Q]\le e^{-s/8}+\frac{2q_R(1+q_H)}{s},
--   $$
--   where $Q$ is the set for the procedure $f(z)$, the function $G$ and $S^+=S\cup\{w\}$.
--
--   The reason is that, given $G,z,S^+$, the point $w$ is uniform on $S^+$, while $Q$ depends only on $G,z,S^+$.
--
--   Differences from the source:
--   - encoding: rho = G|_{S̄} with S the free set (overline on the rendered p.13, p.20) → freeOn G S; reason: notation only, the same partial assignment
--   - reading: x, F chosen canonically depending only on rho+, y → any choice function wit on (rho, y) valid where T_rho(y) = 1; reason: the canonical choice is one such function
--   - generalization: O(q^2/s) and "The total size of Q is O(q^2)", one q, in the setting of Theorem 1 → the explicit 2 qR (1 + qH)/s and qR (1 + qH), for separate qR, qH and every 0 < p <= 1; reason: for q = max(qR, qH) these are O(q^2/s) and O(q^2); the separate bounds are needed since Lemma 3 changes only R
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), proof of Theorem 1, p.21

import Definitions.Def_StretchDepth_Qset

namespace StretchDepth

/-- **Proof of Theorem 1: the probability of `w ∈ Q`.**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), proof of Theorem 1, p.21: "Conditioned on G, z, S+ the distribution of w is uniform on S+, so
we have Pr[w ∈ Q] ≤ EG,z,S+ |Q ∩ S+| / |S+| ≤ Pr[|S+| < s/2] + O(q2/s) ≤ e−s/8 + O(q2/s)".

**Formalization Note.** `s = p 2^n`. With `qR` a query bound of the procedures and `qH` of the
construction, "The total size of Q is O(q2)" (p.20) is `|Q| ≤ qR(1 + qH)`, and `O(q²/s)` is
`2 qR (1 + qH)/s`. The two bounds are separate because Lemma 3 changes only `R`. -/
theorem prob_mem_Q {n N m M : ℕ} (H : Bits m → RoundTree n N M)
    (wit : PartialAssign n N → Bits M → Bits m × (Bits n → Bits N)) (hwit : IsWitness H wit)
    (f : Bits N → QProc n N M) (qR qH : ℕ)
    (hR : ∀ (z : Bits N) (G : Bits n → Bits N) (T : Bits M → Bool),
      (f z).queries (oracle G T) ≤ qR)
    (hH : ∀ (G : Bits n → Bits N) (x : Bits m), numQueries G (H x) ≤ qH)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (∀ (G : Bits n → Bits N) (Splus : Finset (Bits n)) (z : Bits N),
      (Qset H wit (f z) G Splus).card ≤ qR * (1 + qH)) ∧
    probPlanted p (fun G S w z => w ∈ Qset H wit (f z) G (insert w S)) ≤
      Real.exp (-(p * 2 ^ n) / 8) + 2 * (qR : ℝ) * (1 + (qH : ℝ)) / (p * 2 ^ n) := by sorry

end StretchDepth
