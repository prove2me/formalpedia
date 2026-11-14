-- Prove2me | Theorems.Thm_UpperHalfPlane_bergman_reproducing_formula
-- name    : UpperHalfPlane.bergman_reproducing_formula
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-14T00:25:13.85795+00:00
-- url     : https://prove2.me/theorems/ffabc26a-22a3-4f2e-b163-6e4b5b0e5b85
-- title:
--   Weighted Bergman reproducing formula on the upper half plane for holomorphic $f$ with $|f(z)| \le C\,(\operatorname{Im} z)^{-k/2}$, $k \ge 3$
-- statement:
--   Let $\mathbb H = \{z \in \mathbb C : \operatorname{Im} z > 0\}$ be the upper half plane, write $z = x + iy$, and let $d\mu(z) = \frac{dx\,dy}{y^2}$ be the $\mathrm{SL}_2(\mathbb R)$-invariant hyperbolic measure. Let $k \ge 3$ be an integer and let $f$ be holomorphic on $\mathbb H$ with
--
--   $$|f(z)| \le \frac{C}{y^{k/2}} \qquad (z \in \mathbb H)$$
--
--   for some constant $C$. Then for every $w \in \mathbb H$ the function $z \mapsto f(z)\,\overline{(z - \bar w)^{-k}}\,y^{k}$ is $\mu$-integrable on $\mathbb H$, and
--
--   $$\int_{\mathbb H} f(z)\,\overline{(z - \bar w)^{-k}}\; y^{k}\, \frac{dx\,dy}{y^2} \;=\; \frac{4\pi\, i^{k}}{(k-1)\,2^{k}}\; f(w) \;=\; \frac{\pi\, i^{k}}{(k-1)\,2^{k-2}}\; f(w).$$
--
--   Equivalently, $(z - \bar w)^{-k}$, suitably normalized, is the reproducing kernel of the weighted Bergman space of holomorphic $f$ with $\int_{\mathbb H} |f|^2 y^{k-2}\,dx\,dy < \infty$, here stated for the growth class $|f| \le C y^{-k/2}$ that contains every cusp form of weight $k$.
--
--   Role: this is the reproducing property behind Petersson's theory of Poincare series. Summing it over a Fuchsian group $\Gamma$ (unfolding) shows that the Petersson inner product of a cusp form $f \in S_k(\Gamma)$ with the Poincare-type kernel $\sum_{\gamma} (\gamma z - \bar w)^{-k}(cz+d)^{-k}$ is a fixed multiple of $f(w)$, which is the starting point of Zagier's proof of the Eichler-Selberg trace formula for Hecke operators. Cusp forms satisfy the hypothesis because $y^{k/2}|f(z)|$ is bounded on $\mathbb H$.
--
--   **Formalization Note**: $f$ is a function `ℂ → ℂ` that is complex differentiable on the open set `{z : ℂ | 0 < z.im}`; its values off $\mathbb H$ play no role. The hyperbolic measure is written as Lebesgue measure on $\mathbb C$ restricted to $\{\operatorname{Im} z > 0\}$ times the density $(\operatorname{Im} z)^{-2}$, the last factor `((z.im : ℂ) ^ 2)⁻¹` of the integrand. `starRingEnd ℂ` is complex conjugation and `y ^ ((k : ℝ) / 2)` is the real power $y^{k/2}$. The statement asserts integrability as well as the value, so the Bochner integral is a genuine absolutely convergent integral. Example: $f(z) = (z + i)^{-k}$ satisfies the hypothesis with $C = 1$.
-- source:
--   H. Petersson, Einheitliche Begruendung der Vollstaendigkeitssaetze fuer die Poincareschen Reihen von reeller Dimension bei beliebigen Grenzkreisgruppen von erster Art, Abh. Math. Sem. Hamburg 14 (1941); D. Zagier, Modular forms whose Fourier coefficients involve zeta-functions of quadratic fields, in Modular Functions of One Variable VI, LNM 627 (1977), Proposition 1; H. Iwaniec, Topics in Classical Automorphic Forms, AMS GSM 17 (1997), Section 2.6; H. Hedenmalm, B. Korenblum, K. Zhu, Theory of Bergman Spaces, GTM 199 (2000), Section 1.1

import Mathlib

set_option autoImplicit false

theorem UpperHalfPlane.bergman_reproducing_formula (k : ℕ) (hk : 3 ≤ k) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im}) (C : ℝ)
    (hC : ∀ z : ℂ, 0 < z.im → ‖f z‖ ≤ C / z.im ^ ((k : ℝ) / 2)) (w : ℂ) (hw : 0 < w.im) :
    MeasureTheory.IntegrableOn
        (fun z : ℂ => f z * starRingEnd ℂ (((z - starRingEnd ℂ w) ^ k)⁻¹) * (z.im : ℂ) ^ k *
          ((z.im : ℂ) ^ 2)⁻¹)
        {z : ℂ | 0 < z.im} ∧
      ∫ z in {z : ℂ | 0 < z.im},
          f z * starRingEnd ℂ (((z - starRingEnd ℂ w) ^ k)⁻¹) * (z.im : ℂ) ^ k * ((z.im : ℂ) ^ 2)⁻¹ =
        4 * (Real.pi : ℂ) * Complex.I ^ k / (((k : ℂ) - 1) * 2 ^ k) * f w := by sorry
